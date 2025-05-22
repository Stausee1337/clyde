use std::{cell::Cell, fmt::Write};

use hashbrown::HashMap;
use num_traits::ToPrimitive;

use crate::{context::TyCtxt, diagnostics::{DiagnosticsCtxt, Message}, syntax::{ast::{self, DefId, DefinitionKind, NodeId}, lexer::{self, Span}, symbol::sym}, type_ir::{self, AdtDef, AdtKind, ConstKind, Integer, Ty, TyKind}};

#[derive(Clone, Copy)]
enum Expectation<'tcx> {
    None,
    Coerce(Ty<'tcx>),
    Guide(Ty<'tcx>)
}

impl<'tcx> From<Option<Ty<'tcx>>> for Expectation<'tcx> {
    fn from(value: Option<Ty<'tcx>>) -> Self {
        match value {
            Some(ty) => Expectation::Coerce(ty),
            None => Expectation::None
        }
    }
}

/// NOTE: This is very finicky (because I copied the Diverges
/// handling from rustc). The only reason statements
/// show up correctly in `NOTE: ...` diagnostics is because 
/// `lexer::Span` is implementing `Ord` by comparing Span lengths.
/// Longer, more high-level Spans get priorotized over shorter,
/// more nested ones, making the "larger Node win".
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Diverges {
    Maybe,
    Always(Span),
    WarnedAlways
}

#[derive(Debug)]
struct LoopCtxt {
    owner: NodeId,
    may_break: bool
}

#[derive(Debug)]
struct BlockCtxt<'tcx> {
    owner: NodeId,
    result_ty: Option<Ty<'tcx>>
}

impl<'tcx> BlockCtxt<'tcx> {
    fn new(node_id: NodeId) -> Self {
        Self {
            owner: node_id,
            result_ty: None
        }
    }
}

struct TypecheckCtxt<'tcx> {
    tcx: TyCtxt<'tcx>,
    return_ty: Option<Ty<'tcx>>,
    diverges: Cell<Diverges>,
    loop_stack: Vec<LoopCtxt>,
    block_stack: Vec<BlockCtxt<'tcx>>,
    field_indices: HashMap<ast::NodeId, type_ir::FieldIdx>,
    lowering_ctxt: LoweringCtxt<'tcx>,
}

impl<'tcx> TypecheckCtxt<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            return_ty: None,
            diverges: Cell::new(Diverges::Maybe),
            loop_stack: Vec::new(),
            block_stack: Vec::new(),
            field_indices: Default::default(),
            lowering_ctxt: LoweringCtxt::new(tcx, LoweringMode::Body),
        }
    }

    fn diagnostics(&self) -> &DiagnosticsCtxt {
        self.tcx.diagnostics()
    }

    fn enter_loop_ctxt<F: FnOnce(&mut Self) -> T, T>(&mut self, ctxt: LoopCtxt, do_work: F) -> (LoopCtxt, T) {
        self.loop_stack.push(ctxt);
        let rv = do_work(self);
        let ctxt = self.loop_stack.pop().unwrap();
        (ctxt, rv)
    }

    fn loop_ctxt(&mut self, owner: NodeId) -> Option<&mut LoopCtxt> {
        for ctxt in &mut self.loop_stack {
            if ctxt.owner == owner {
                return Some(ctxt);
            }
        }
        None
    }

    fn enter_block_ctxt<F: FnOnce(&mut Self) -> T, T>(&mut self, node_id: NodeId, do_work: F) -> (BlockCtxt<'tcx>, T) {
        self.block_stack.push(BlockCtxt::new(node_id));
        let rv = do_work(self);
        let ctxt = self.block_stack.pop().unwrap();
        (ctxt, rv)
    }

    fn block_ctxt(&mut self) -> Option<&mut BlockCtxt<'tcx>> {
        self.block_stack.last_mut()
    }

    fn autoderef(&self, mut ty: Ty<'tcx>, level: i32) -> Option<Ty<'tcx>> {
        let mut idx = 0;
        while idx != level {
            match ty {
                Ty(type_ir::TyKind::Refrence(base)) => {
                    if idx == level - 1 {
                        return Some(*base);
                    }
                    ty = *base;
                },
                Ty(type_ir::TyKind::Err | type_ir::TyKind::Never) =>
                    return Some(ty),
                _ => break
            }
            idx += 1;
        }
        if level < 0 { // autoderef case
            return Some(ty);
        }
        None
    }
    
    fn deref(&self, ty: Ty<'tcx>, span: Span) -> Ty<'tcx> {
        let Some(deref) = self.autoderef(ty, 1) else {
            Message::error(format!("type {ty} cannot be derefrenced"))
                .at(span)
                .push(self.diagnostics());
            return Ty::new_error(self.tcx);
        };
        deref
    }

    fn check_stmt_if(&mut self, if_stmt: &'tcx ast::If<'tcx>) -> Ty<'tcx> {
        self.check_expr_with_expectation(
            if_stmt.condition, Expectation::Coerce(self.tcx.basic_types.bool));

        self.maybe_warn_unreachable(if_stmt.body.span, "block");

        let cond_diverges = self.diverges.replace(Diverges::Maybe);

        let mut body_ty = self.check_block(&if_stmt.body, Expectation::None);
        let body_diverges = self.diverges.replace(Diverges::Maybe);

        if let Some(else_branch) = if_stmt.else_branch {
            let else_ty = self.check_stmt(else_branch);
            let else_diverges = self.diverges.get();

            body_ty = self.maybe_emit_type_error(else_ty, body_ty, else_branch.span);

            self.diverges.set(std::cmp::max(cond_diverges, std::cmp::min(body_diverges, else_diverges)));
        } else {
            self.diverges.set(cond_diverges);
            body_ty = self.tcx.basic_types.void;
        }

        // self.diverges.set(std::cmp::max(self.diverges.get(), prev_diverge));

        body_ty
    }

    fn check_stmt_while(&mut self, while_loop: &'tcx ast::While<'tcx>, node_id: NodeId) -> Ty<'tcx> {

        let res = self.check_expr_with_expectation(while_loop.condition, Expectation::Coerce(self.tcx.basic_types.bool));

        self.maybe_warn_unreachable(while_loop.body.span, "block");

        let cond_diverges = self.diverges.replace(Diverges::Maybe);

        let mut endless = false;
        // TODO: replace with propper compile time constant evaluation
        if res == self.tcx.basic_types.bool && matches!(while_loop.condition.kind, ast::ExprKind::Literal(ast::Literal::Boolean(true))) {
            endless = true;
        }

        let ctxt = LoopCtxt {
            owner: node_id, may_break: false
        };

        let (ctxt, ()) = self.enter_loop_ctxt(ctxt, |this| {
            this.check_block(&while_loop.body, Expectation::Coerce(this.tcx.basic_types.void));
        });

        if !endless || ctxt.may_break {
            self.diverges.set(std::cmp::max(cond_diverges, Diverges::Maybe));
            return self.tcx.basic_types.void;
        }

        self.tcx.basic_types.never
    }

    fn check_stmt_for(&mut self, for_loop: &'tcx ast::For<'tcx>, node_id: NodeId) -> Ty<'tcx> {

        let iter_ty  = self.check_expr_with_expectation(for_loop.iterator, Expectation::None);

        self.maybe_warn_unreachable(for_loop.body.span, "block");

        let iter_diverges = self.diverges.replace(Diverges::Maybe);

        let base = {
            use type_ir::TyKind::{Never, Err, Slice, Array, DynamicArray, Range, Refrence};

            if let Ty(Never | Err) = iter_ty {
                iter_ty
            } else if let Ty(Slice(base) | Array(base, _) | DynamicArray(base) | Range(base, _)) = self.autoderef(iter_ty, 1).unwrap_or(iter_ty) {
                if let Ty(Refrence(..)) = iter_ty {
                    Ty::new_refrence(self.tcx, *base)
                } else {
                    *base
                }
            } else {
                Message::error(format!("expected iterable, found {iter_ty}"))
                    .at(for_loop.iterator.span)
                    .push(self.diagnostics());
                Ty::new_error(self.tcx)
            }
        };

        self.ty_local(node_id, base);

        let ctxt = LoopCtxt {
            owner: node_id, may_break: false
        };

        let (_, ()) = self.enter_loop_ctxt(ctxt, |this| {
            this.check_block(&for_loop.body, Expectation::Coerce(this.tcx.basic_types.void));
        });

        self.diverges.set(std::cmp::max(iter_diverges, Diverges::Maybe));

        self.tcx.basic_types.void
    }

    fn check_stmt_local(&mut self, stmt: &'tcx ast::Stmt<'tcx>, local: &'tcx ast::Local<'tcx>) -> Ty<'tcx> {
        let expected = local.ty.map(|ty| self.lower_ty(&ty));

        if let Some(expected) = expected {
            if expected.is_incomplete() {
                let span = local.ty.unwrap().span;
                Message::fatal(format!("type infrence in local variables is not supported"))
                    .at(span)
                    .push(self.diagnostics());
            }
        }

        if expected.is_none() && local.init.is_none() {
            Message::error("type-anonymous variable declarations require an init expresssion")
                .at(stmt.span)
                .push(self.diagnostics());
            let ty = Ty::new_error(self.tcx);
            self.ty_local(stmt.node_id, ty);
            self.tcx.basic_types.void
        } else if let Some(expr) = local.init {
            let ty = self.check_expr_with_expectation(expr, expected.into());
            self.ty_local(stmt.node_id, expected.unwrap_or(ty));
            if let Ty(type_ir::TyKind::Never) = ty {
                return ty;
            }
            self.tcx.basic_types.void
        } else if let Some(expected) = expected {
            self.ty_local(stmt.node_id, expected);
            self.tcx.basic_types.void
        } else {
            unreachable!()
        }
    }

    fn check_stmt(&mut self, stmt: &'tcx ast::Stmt) -> Ty<'tcx> {
        match &stmt.kind {
            ast::StmtKind::Expr(expr) => {
                let ty = self.check_expr_with_expectation(expr, Expectation::None);
                if let Ty(type_ir::TyKind::Never) = ty {
                    return ty;
                }
            }
            ast::StmtKind::If(if_stmt) =>
                return self.check_stmt_if(if_stmt),
            ast::StmtKind::While(while_loop) =>
                return self.check_stmt_while(while_loop, stmt.node_id),
            ast::StmtKind::For(for_loop) =>
                return self.check_stmt_for(for_loop, stmt.node_id),
            ast::StmtKind::Local(local) =>
                return self.check_stmt_local(stmt, local),
            ast::StmtKind::Block(block) =>
                return self.check_block(block, Expectation::None),
            ast::StmtKind::Return(expr) => {
                let Some(return_ty) = self.return_ty else {
                    Message::error("`return` found outside of function body")
                        .at(stmt.span)
                        .note("use yeet ...; for producing values")
                        .push(self.diagnostics());
                    return Ty::new_error(self.tcx);
                };
                let ty = expr
                    .as_ref()
                    .map(|expr| self.check_expr_with_expectation(expr, Expectation::Coerce(return_ty)));
                if let None = ty {
                    let ty = self.tcx.basic_types.void;
                    self.maybe_emit_type_error(ty, return_ty, stmt.span);
                }
                return self.tcx.basic_types.never;
            }
            ast::StmtKind::ControlFlow(flow) => {
                if let Ok(owner) = flow.destination.get().expect("owner or error resolved during resolution phase") {
                    if flow.kind == ast::ControlFlowKind::Break {
                        let ctxt = self.loop_ctxt(*owner).expect("loop destination for break;");
                        ctxt.may_break = true;
                    }
                    return self.tcx.basic_types.never;
                } else {
                    return Ty::new_error(self.tcx);
                }
            }
            ast::StmtKind::Yeet(yeet) => {
                let Some(block_ctxt) = self.block_ctxt() else {
                    yeet.owner.set(Err(ast::OutsideScope)).unwrap();
                    Message::error("`yeet` found outside of block expression")
                        .at(stmt.span)
                        .note("use return ...; to return a value from a function")
                        .push(self.diagnostics());
                    return Ty::new_error(self.tcx);
                };
                // FIXME: resolve yeet expressions at resolve pass like we should
                yeet.owner.set(Ok(block_ctxt.owner)).unwrap();

                let expected = block_ctxt.result_ty;
                let expectation = expected.into();
                let ty = yeet.expr.map(|expr| self.check_expr_with_expectation(expr, expectation));

                match (ty, expected) {
                    (None, Some(expected)) => {
                        self.maybe_emit_type_error(self.tcx.basic_types.void, expected, stmt.span);
                    }
                    (Some(found), None) => {
                        let block_ctxt = self.block_ctxt().unwrap();
                        block_ctxt.result_ty = Some(found);
                    }
                    (None, None) => {
                        let void = self.tcx.basic_types.void;
                        let block_ctxt = self.block_ctxt().unwrap();
                        block_ctxt.result_ty = Some(void);
                    },
                    (Some(..), Some(..)) => (), // expression already typechecked
                }
                return self.tcx.basic_types.never;
            }
            ast::StmtKind::Item(_item) => (),
            ast::StmtKind::Err => (),
        }
        self.tcx.basic_types.void
    }

    fn check_expr_integer(&mut self, int: ast::Integer, expected: Option<Ty<'tcx>>, span: Span) -> Ty<'tcx> {
        let mut min_int = if int.signed {
            let Some(int) = Integer::fit_signed(-(int.value as i128)) else {
                Message::error(format!("{} does not fit into signed long", int.value))
                    .at(span)
                    .push(self.diagnostics());
                return Ty::new_error(self.tcx);
            };
            int
        } else {
            Integer::fit_unsigned(int.value)
        };

        // check if there is an expectation and that the singed requirements hold, which are:
        //      - the integers are the same signedness
        //      - or a signed value as expected, but an unsigned value was provided
        if let Some(expected @ Ty(type_ir::TyKind::Int(integer, signed))) = expected && *signed | !int.signed {
            let min_int = if *signed {
                Integer::fit_signed((int.value as i128) * if int.signed { -1 } else { 1 }).map_or(type_ir::Size::from_bits(128), |i| i.size(&self.tcx))
            } else {
                Integer::fit_unsigned(int.value).size(&self.tcx)
            };
            if integer.size(&self.tcx) >= min_int {
                return expected;
            }
        }

        if min_int.size(&self.tcx) < Integer::I32.size(&self.tcx) {
            min_int = Integer::I32;
        }

        let mut signed = int.signed;
        if !int.signed && Integer::fit_signed(int.value as i128).is_some() {
            signed = true;
        }

        Ty::new_int(self.tcx, min_int, signed)
    }

    fn check_block(&mut self, block: &'tcx ast::Block, expectation: Expectation<'tcx>) -> Ty<'tcx> {
        for stmt in block.stmts {
            self.maybe_warn_unreachable(stmt.span, "statement");

            let prev_diverge = self.diverges.replace(Diverges::Maybe);
            let ty = self.check_stmt(stmt);
            self.ty_assoc(stmt.node_id, ty);

            if let Ty(type_ir::TyKind::Never) = ty {
                self.diverges.set(std::cmp::max(self.diverges.get(), Diverges::Always(stmt.span)));
            }
            let current_diverge = self.diverges.get();
            self.diverges.set(std::cmp::max(current_diverge, prev_diverge));
        }

        let ty = if let Diverges::Maybe = self.diverges.get() {
            self.tcx.basic_types.void
        } else {
            self.tcx.basic_types.never
        };


        if let Expectation::Coerce(expected) = expectation {
            self.maybe_emit_type_error(ty, expected, block.span)
        } else {
            ty
        }
    }

    /// Checks wether a specific Expr has a definite type, basically checking for integer
    ///
    /// Recurses the depth of expression Expr until the type either needs to be definite,
    /// or an integer was found
    fn check_expr_ty_definite(&self, kind: &'tcx ast::ExprKind) -> bool {
        use ast::Literal as Cnst;
        match kind {
            ast::ExprKind::BinaryOp(binop) =>
                self.check_expr_ty_definite(&binop.lhs.kind) && self.check_expr_ty_definite(&binop.rhs.kind),
            ast::ExprKind::AssignOp(assign) =>
                self.check_expr_ty_definite(&assign.lhs.kind) && self.check_expr_ty_definite(&assign.rhs.kind),
            ast::ExprKind::Cast(cast) => cast.ty.is_some(),
            ast::ExprKind::UnaryOp(unary) => self.check_expr_ty_definite(&unary.expr.kind),
            ast::ExprKind::Range(range) =>
                self.check_expr_ty_definite(&range.start.kind) && self.check_expr_ty_definite(&range.end.kind),
            ast::ExprKind::Literal(Cnst::Null | Cnst::Integer(..)) => false,
            ast::ExprKind::Tuple(exprs) => {
                for expr in *exprs {
                    if !self.check_expr_ty_definite(&expr.kind) {
                        return false;
                    }
                }
                true
            }
            ast::ExprKind::Block(_) => true, // block is to complicated, so it's going to be matched
            ast::ExprKind::FunctionCall(..) | ast::ExprKind::TypeInit(..) |
            ast::ExprKind::Subscript(..) | ast::ExprKind::Field(..) |
            ast::ExprKind::Path(..) | ast::ExprKind::Deref(..) |
            ast::ExprKind::Literal(..) | ast::ExprKind::Err => true,
        }
    }

    fn check_op_between(&self, op: lexer::BinaryOp, lhs: Ty<'tcx>, rhs: Ty<'tcx>) -> Option<Ty<'tcx>> {
        use lexer::BinaryOp::*;

        macro_rules! boolop {
            ($ret:expr) => {{
                if let GreaterThan | GreaterEqual | LessThan | LessEqual = op {
                    return Some(self.tcx.basic_types.bool);
                }
                return Some($ret);
            }};
        }

        let (Plus | Minus | Mul | Div | Mod |
             LeftShift | RightShift | BitwiseAnd | BitwiseOr | BitwiseXor |
             GreaterThan | GreaterEqual | LessThan | LessEqual) = op else {
            panic!("check_op_between used on invalid operator {op:?}");
        };
        fn get_int(ty: Ty<'_>) -> Option<Ty<'_>> {
            match ty { 
                Ty(type_ir::TyKind::Int(..)) => Some(ty),
                _ => None,
            }
        }

        if let Some(bendable) = Ty::with_bendable(&[lhs, rhs]) {
            return Some(bendable);
        }

        // ptr arithmetic: ptr + int, ptr - int
        if let Ty(type_ir::TyKind::Refrence(..)) = lhs &&
            let Ty(type_ir::TyKind::Int(..)) = rhs &&
            let Plus | Minus = op {
            return Some(lhs);
        }

        // ptr arithmetic: ptr - ptr
        if let Ty(type_ir::TyKind::Refrence(lhs_ty)) = lhs &&
            let Ty(type_ir::TyKind::Refrence(rhs_ty)) = rhs &&
            let Minus = op &&
            lhs_ty == rhs_ty {
            return Some(lhs);
        }

        // ptr comparison: ptr {cmp} ptr, where {cmp}: Gt, Ge, Lt, Le
        if let Ty(type_ir::TyKind::Refrence(lhs_ty)) = lhs &&
            let Ty(type_ir::TyKind::Refrence(rhs_ty)) = rhs &&
            let GreaterThan | GreaterEqual | LessThan | LessEqual = op &&
            lhs_ty == rhs_ty {
            return Some(self.tcx.basic_types.bool);
        }

        // integer arithmetic
        let Some((lhs_int, rhs_int)) = Option::zip(get_int(lhs), get_int(rhs)) else {
            return None;
        };

        if lhs_int == rhs_int {
            boolop!(lhs_int);
        }
        

        return None;
    }

    fn check_expr_assignop(&mut self, assign: &'tcx ast::AssignOp<'tcx>, expected: Option<Ty<'tcx>>) -> Ty<'tcx> {
        let is_valid_lhs = {
            use ast::ExprKind::{Subscript, Field, Path, Deref};
            matches!(assign.lhs.kind, Subscript(..) | Field(..) | Path(..) | Deref(..)) 
        };
        if !is_valid_lhs {
            Message::error("invalid left hand side in assignment")
                .at(assign.lhs.span)
                .push(self.diagnostics());
        }
        // FIXME: handle different assignment operators
        let lhs_ty = self.check_expr_with_expectation(assign.lhs, expected.into());
        if let Ty(type_ir::TyKind::Never) = self.check_expr_with_expectation(assign.rhs, Expectation::Coerce(lhs_ty)) {
            self.diverges.set(Diverges::Always(assign.rhs.span));
        }
        lhs_ty
    }

    fn check_expr_binop(&mut self, binop: &'tcx ast::BinaryOp<'tcx>, span: Span, expected: Option<Ty<'tcx>>) -> Ty<'tcx> {
        use lexer::BinaryOp::*;
        match binop.operator {
            Plus | Minus | Mul | Div | Mod |
            LeftShift | RightShift | BitwiseAnd | BitwiseOr | BitwiseXor => {
                {
                    let mut lhs = &binop.lhs;
                    let mut rhs = &binop.rhs;
                    if !self.check_expr_ty_definite(&lhs.kind) && self.check_expr_ty_definite(&rhs.kind) {
                        (lhs, rhs) = (rhs, lhs);
                    }

                    let expectation = match expected {
                        Some(ty) => Expectation::Guide(ty),
                        None => Expectation::None
                    };
                    let lhs_ty = self.check_expr_with_expectation(lhs, expectation);
                    self.check_expr_with_expectation(rhs, Expectation::Guide(lhs_ty));
                }
                let lhs_ty = self.associations[&binop.lhs.node_id];
                let rhs_ty = self.associations[&binop.rhs.node_id];
                let Some(ret_ty) = self.check_op_between(binop.operator, lhs_ty, rhs_ty) else {
                    Message::error(
                        format!("operation {} is not defined between {lhs_ty} and {rhs_ty}", binop.operator))
                        .at(span)
                        .push(self.diagnostics());
                    return Ty::new_error(self.tcx);
                };
                return ret_ty;
            }
            Equals | NotEquals => {
                let mut lhs = &binop.lhs;
                let mut rhs = &binop.rhs;
                if !self.check_expr_ty_definite(&lhs.kind) && self.check_expr_ty_definite(&rhs.kind) {
                    (lhs, rhs) = (rhs, lhs);
                }

                // BUG: it seems logiacl that any two values of the same type should be comparable
                // for equality, but this practicly needs quite some extra logic to polymorphically
                // work for any two types. Of course there are the primitives (which are easily
                // comparable), but anything else would need an emit during IR generation to a
                // generically overloaded `eq` operator doing a memcmp. We obviously can't do that
                // yet, so this will crash at codegen stage.

                let ty = self.check_expr_with_expectation(lhs, Expectation::None);
                self.check_expr_with_expectation(rhs, Expectation::Coerce(ty));
                return self.tcx.basic_types.bool;
            }
            GreaterThan | GreaterEqual | LessThan | LessEqual => {
                {
                    let mut lhs = &binop.lhs;
                    let mut rhs = &binop.rhs;
                    if !self.check_expr_ty_definite(&lhs.kind) && self.check_expr_ty_definite(&rhs.kind) {
                        (lhs, rhs) = (rhs, lhs);
                    }

                    let expectation = match expected {
                        Some(ty) => Expectation::Guide(ty),
                        None => Expectation::None
                    };
                    let lhs_ty = self.check_expr_with_expectation(lhs, expectation);
                    self.check_expr_with_expectation(rhs, Expectation::Guide(lhs_ty));
                }
                let lhs_ty = self.associations[&binop.lhs.node_id];
                let rhs_ty = self.associations[&binop.rhs.node_id];
                let Some(ret_ty) = self.check_op_between(binop.operator, lhs_ty, rhs_ty) else {
                    Message::error(
                        format!("operation {} is not defined between {lhs_ty} and {rhs_ty}", binop.operator))
                        .at(span)
                        .push(self.diagnostics());
                    return Ty::new_error(self.tcx);
                };
                {
                    use type_ir::TyKind::{Bool, Err, Never};
                    assert!(
                        matches!(ret_ty, Ty(Bool | Err | Never)),
                        "some equality comparison does not produce boolean");
                }
                return self.tcx.basic_types.bool;
            }
            BooleanAnd | BooleanOr => {
                self.check_expr_with_expectation(
                    &binop.lhs, Expectation::Coerce(self.tcx.basic_types.bool));

                self.check_expr_with_expectation(
                    &binop.rhs, Expectation::Coerce(self.tcx.basic_types.bool));

                return self.tcx.basic_types.bool;
            }
        }
    }

    fn check_expr_unary(&mut self, unary: &'tcx ast::UnaryOp<'tcx>, expected: Option<Ty<'tcx>>) -> Ty<'tcx> {
        match unary.operator {
            lexer::UnaryOp::Minus => {
                use type_ir::TyKind::{Err, Never, Int};

                let expectation = match expected {
                    Some(expected) => Expectation::Guide(expected),
                    None => Expectation::None
                };
                let ty = self.check_expr_with_expectation(unary.expr, expectation);
                let Ty(Int(_, /* signed */ true) | Err | Never) = ty else {
                    Message::error(format!("negation `-` is not defined for type {ty}"))
                        .at(unary.expr.span)
                        .push(self.diagnostics());
                    return Ty::new_error(self.tcx);
                };
                ty
            }
            lexer::UnaryOp::BitwiseNot => {
                use type_ir::TyKind::{Err, Never, Int};

                let expectation = match expected {
                    Some(expected) => Expectation::Guide(expected),
                    None => Expectation::None
                };
                let ty = self.check_expr_with_expectation(unary.expr, expectation);
                let Ty(Int(_, _) | Err | Never) = ty else {
                    Message::error(format!("invert `~` is not defined for type {ty}"))
                        .at(unary.expr.span)
                        .push(self.diagnostics());
                    return Ty::new_error(self.tcx);
                };
                ty
            }
            lexer::UnaryOp::Not => {
                self.check_expr_with_expectation(unary.expr, Expectation::Coerce(self.tcx.basic_types.bool))
            }
            lexer::UnaryOp::Ref => {
                let expectation = match expected {
                    Some(Ty(type_ir::TyKind::Refrence(ty))) => Expectation::Guide(*ty),
                    _ => Expectation::None
                };
                let ty = self.check_expr_with_expectation(unary.expr, expectation);
                if let Ty(type_ir::TyKind::Err | type_ir::TyKind::Never) = ty {
                    return ty;
                }
                Ty::new_refrence(self.tcx, ty)
            }
        }
    }

    fn check_expr_call(&mut self, call: &'tcx ast::FunctionCall<'tcx>, span: Span) -> Ty<'tcx> {
        let ty = self.check_expr_with_expectation(call.callable, Expectation::None);
        if let Ty(type_ir::TyKind::Never | type_ir::TyKind::Err) = ty {
            return ty;
        }
        let Ty(type_ir::TyKind::Function(fn_def)) = ty else {
            Message::error(format!("expected function, found {ty}"))
                .at(call.callable.span)
                .push(self.diagnostics());
            return Ty::new_error(self.tcx);
        }; 

        let signature = self.tcx.fn_sig(*fn_def);

        let mut arg_count = 0;
        for (idx, arg) in call.args.iter().enumerate() {
            match arg {
                ast::FunctionArgument::Direct(expr) => {
                    arg_count += 1;
                    if let Some(param) = signature.params.get(idx) {
                        self.check_expr_with_expectation(expr, Expectation::Coerce(param.ty));
                    }
                }
                ast::FunctionArgument::Keyword(..) =>
                    todo!()
            }
        }

        if arg_count != signature.params.len() {
            Message::error(
                format!("function {} expected {} arugments, {} were supplied",
                        signature.name.get(), signature.params.len(), arg_count))
                .at(span)
                .push(self.diagnostics());
            self.last_error.set(Some(()));
        }

        signature.returns
    }

    fn check_expr_subscript(&mut self, subscript: &'tcx ast::Subscript<'tcx>) -> Ty<'tcx> {
        let ty = self.check_expr_with_expectation(subscript.expr, Expectation::None);
        let index_span = {
            let start = subscript.args.first().unwrap().span.start;
            let end = subscript.args.last().unwrap().span.end;
            Span { start, end }
        };
        let base;
        {
            use type_ir::TyKind::{Err, Never, Array, DynamicArray, Slice, String, Refrence};
            if let Ty(Err | Never) = ty {
                return ty;
            }
            base = match ty {
                Ty(Array(base, _) | DynamicArray(base) | Slice(base) | Refrence(base)) => *base,
                Ty(String) => self.tcx.basic_types.byte,
                _ => {
                    Message::error(format!("cannot index into value of type {ty}"))
                        .at(index_span)
                        .push(self.diagnostics());
                    return Ty::new_error(self.tcx);
                }
            };
        }

        // later, we'll have operator overloading, but for now it's just arrays, dyn arrays and
        // slices and all of them are index by only one argument
        if subscript.args.len() > 1 { 
            Message::error(
                format!("indexer of type {ty} expected 1 arugment, {} were supplied", subscript.args.len()))
                .at(index_span)
                .push(self.diagnostics());
        }
        let arg = self.check_expr_with_expectation(subscript.args.first().unwrap(), Expectation::Guide(self.tcx.basic_types.nuint));
        if let Ty(type_ir::TyKind::Err | type_ir::TyKind::Never) = arg {
            return arg;
        }

        if let Ty(type_ir::TyKind::Int(_, signed)) = arg {
            if !signed {
                return base;
            }
        }
        Message::error(
            format!("mismatched types: expected unsigned integer, found {arg}"))
            .at(index_span)
            .push(self.diagnostics());
        Ty::new_error(self.tcx)
    }

    fn check_expr_ftuple(&mut self, ty: Ty<'tcx>, idx: usize, span: Span) -> Ty<'tcx> {
        let Ty(type_ir::TyKind::Tuple(tys)) = self.autoderef(ty, -1).unwrap_or(ty) else {
            Message::error(format!("unnamed fields are only found on tuples {ty}"))
                .at(span)
                .push(self.diagnostics());
            return Ty::new_error(self.tcx);
        };

        if idx >= tys.len() {
            Message::error(format!("can't find field `{idx}` on {ty}"))
                .at(span)
                .push(self.diagnostics());
            return Ty::new_error(self.tcx);
        }

        tys[idx]
    }

    fn check_expr_field(&mut self, field: &'tcx ast::Field<'tcx>, node_id: ast::NodeId) -> Ty<'tcx> {
        let ty = self.check_expr_with_expectation(field.expr, Expectation::None); 
        if let Ty(type_ir::TyKind::Never | type_ir::TyKind::Err) = ty {
            return ty;
        }
        let field_ident = match &field.field {
            ast::FieldIdent::Named(ident) => ident,
            ast::FieldIdent::Tuple { value, span } =>
                return self.check_expr_ftuple(ty, *value as usize, *span),
        };
        let Ty(type_ir::TyKind::Adt(adt)) = self.autoderef(ty, -1).unwrap_or(ty) else {
            Message::error(format!("fields are only found on structs, not {ty}"))
                .at(field.expr.span)
                .push(self.diagnostics());
            return Ty::new_error(self.tcx);
        };

        let field = match adt {
            AdtDef(AdtKind::Struct(strct)) =>
                strct
                .fields()
                .find(|(_, def)| def.symbol == field_ident.symbol),
            _ => {
                Message::error(format!("fields are only found on structs, not on {}s", adt.kind()))
                    .at(field.expr.span)
                    .push(self.diagnostics());
                return Ty::new_error(self.tcx);
            }
        };

        let Some((idx, field)) = field else {
            Message::error(format!("can't find field `{}` on struct {ty}", field_ident.symbol.get()))
                .at(field_ident.span)
                .push(self.diagnostics());
            return Ty::new_error(self.tcx);
        };

        self.field_indices.insert(node_id, idx);
        self.tcx.type_of(field.def)
    }
 
    fn check_expr_init(
        &mut self, ty_init: &'tcx ast::TypeInit<'tcx>, span: Span) -> Ty<'tcx> {
        let ty = self.lower_ty(ty_init.ty);
        
        use type_ir::TyKind::{self, Int, Float, Char, Bool, Void, String};
        match ty {
            Ty(Int(..) | Float(..) | Char | Bool | Void | String) => {
                Message::error(format!("expected struct, found primitive {ty}"))
                    .at(span)
                    .note("initialze primitive directly")
                    .push(self.diagnostics());
                self.last_error.set(Some(()));
            }
            Ty(TyKind::Refrence(..)) => {
                Message::error(format!("expected struct, found {ty}"))
                    .at(span)
                    .push(self.diagnostics());
                return Ty::new_error(self.tcx);
            }
            Ty(TyKind::Slice(..)) => {
                Message::error(format!("expected struct, found slice {ty}"))
                    .at(span)
                    .note("initialize a fixed or dynamic array")
                    .push(self.diagnostics());
                self.last_error.set(Some(()));
            }
            Ty(TyKind::Tuple(..)) => {
                Message::error(format!("expected struct, found tuple {ty}"))
                    .at(span)
                    .note("initialize tuple using tuple expression (<0>, <1>, ...)")
                    .push(self.diagnostics());
                self.last_error.set(Some(()));
            }
            Ty(kind @ (TyKind::Array(base, _) | TyKind::DynamicArray(base))) => {
                for init in ty_init.initializers {
                    match init {
                        ast::TypeInitKind::Direct(expr) => {
                            self.check_expr_with_expectation(expr, Expectation::Coerce(*base));
                        }
                        ast::TypeInitKind::Field(ident, expr) => {
                            Message::error("field initializer in array initialization is invalid")
                                .at(Span::new(ident.span.start, expr.span.end))
                                .push(self.diagnostics());
                            self.last_error.set(Some(()));
                        }
                    }
                }
                
                let count = ty_init.initializers.len() as u64;
                match kind {
                    type_ir::TyKind::Array(_, capcity) => {
                        let capacity = capcity.downcast_unsized::<dyn ToPrimitive>()
                            .map(|p| p.to_u64())
                            .flatten()
                            .expect("array has capacity of usize");
                        if count != 0 && count != 1 && count != capacity {
                            Message::error(format!("expected array with {capacity} elements, found {count} elements"))
                                .at(span)
                                .push(self.diagnostics());
                            self.last_error.set(Some(()));
                        }
                    }
                    _ => ()
                }
            }
            Ty(TyKind::Enum(enm)) => {
                Message::error(format!("expected struct, found enum {ty}"))
                    .at(span)
                    .note(format!("create an enum value using `{}::<Variant>` syntax", enm.name.get()))
                    .push(self.diagnostics());
                self.last_error.set(Some(()));
            }
            Ty(TyKind::Param(_)) => {
                Message::error(format!("expected struct, found type paramaeter `{ty}`"))
                    .at(span)
                    .push(self.diagnostics());
                self.last_error.set(Some(()));
            }
            Ty(TyKind::Adt(adt)) => match adt {
                AdtDef(type_ir::AdtKind::Struct(strct)) => {
                    // FIXME: Don't build reverse field lookup every time
                    // we need to lookup fields
                    // TODO: refactor into ctxt function
                    let fields: HashMap<_, _> = strct.fields()
                        .map(|(idx, fdef)| (fdef.symbol, (idx, fdef)))
                        .collect();

                    for init in ty_init.initializers {
                        match init {
                            ast::TypeInitKind::Field(ident, expr) => {
                                let Some((idx, fdef)) = fields.get(&ident.symbol) else {
                                    Message::error(format!("can't find field `{}` on struct {ty}", ident.symbol.get()))
                                        .at(ident.span)
                                        .push(self.diagnostics());
                                    continue;
                                };
                                let fty = self.tcx.type_of(fdef.def);
                                self.check_expr_with_expectation(expr, Expectation::Coerce(fty));
                                self.field_indices.insert(expr.node_id, *idx);
                            }
                            ast::TypeInitKind::Direct(expr) if let ast::ExprKind::Path(path) = &expr.kind => {
                                todo!("struct init quality of live improvement");
                                /*let Some((idx, fdef)) = fields.get(&path) else {
                                    Message::error(format!("can't find field `{}` on struct {ty}", name.ident.symbol.get()))
                                        .at(name.ident.span)
                                        .push(self.diagnostics());
                                    self.last_error.set(Some(()));
                                    continue;
                                };
                                let fty = self.tcx.type_of(fdef.def);
                                self.check_expr_with_expectation(expr, Expectation::Coerce(fty));
                                self.field_indices.insert(expr.node_id, *idx);*/
                            }
                            ast::TypeInitKind::Direct(expr) => {
                                Message::error("immediate initializer in struct initialization is invalid")
                                    .at(expr.span)
                                    .push(self.diagnostics());
                                self.last_error.set(Some(()));
                            }
                        }
                    }
                }
                AdtDef(type_ir::AdtKind::Union) => todo!()
            }
            Ty(TyKind::Function(..)) => unreachable!(),
            Ty(TyKind::Range(..)) => unreachable!(),
            Ty(TyKind::Never | TyKind::Err) => ()
        }

        ty
    }

    fn check_valid_cast(&self, from: Ty<'tcx>, to: Ty<'tcx>) -> bool {
        use type_ir::TyKind::{Err, Never, Int, Refrence, Array, Float, Char, Bool};
        if let Ty(Err | Never) = from {
            return true;
        }
        if let Ty(Err | Never) = to {
            return true;
        }

        if let (Ty(Int(..) | Float(..)), Ty(Int(..) | Float(..))) = (to, from) {
            return true;
        }
        if let (Ty(Int(..) | Refrence(..)), Ty(Int(..) | Refrence(..))) = (to, from) {
            return true;
        }

        return match (from, to) {
            (Ty(Int(..)), Ty(Bool)) => true,
            (Ty(Bool), Ty(Int(..))) => true,

            (Ty(Int(Integer::I32 | Integer::I8, false)), Ty(Char)) => true,
            (Ty(Char), Ty(Int(Integer::I32 | Integer::I8, false))) => true,

            (Ty(Array(aty, _)), Ty(Refrence(rty))) if aty == rty => true,
            _ => false
        };
    }

    fn check_expr_cast(&mut self, cast: &'tcx ast::Cast<'tcx>, expected: Option<Ty<'tcx>>, span: Span) -> Ty<'tcx> {

        let ty = cast.ty.map(|expr| self.lower_ty(expr));
        
        let Some(ty) = ty.or(expected) else {
            let tc = match cast.kind {
                ast::TypeConversion::Cast => "cast",
                ast::TypeConversion::Transmute => "transmute",
            };
            Message::error(format!("can't infer type of auto {}", tc))
                .at(span)
                .push(self.diagnostics());
            return Ty::new_error(self.tcx);
        };

        let expr_ty = self.check_expr_with_expectation(cast.expr, Expectation::None);

        match cast.kind {
            ast::TypeConversion::Cast => {
                if !self.check_valid_cast(expr_ty, ty) {
                    Message::error(
                        format!("no cast is defined from {expr_ty} to {ty}"))
                        .at(span)
                        .push(self.diagnostics());
                    self.last_error.set(Some(()));
                }
            }
            ast::TypeConversion::Transmute => {
                todo!("Idk how to do that righ now");
            }
        }

        ty
    }

    fn check_expr_tuple(&mut self, exprs: &'tcx [&'tcx ast::Expr<'tcx>], expected: Option<Ty<'tcx>>) -> Ty<'tcx> {
        let expected_list = match expected {
            Some(Ty(type_ir::TyKind::Tuple(tys))) => Some(tys),
            _ => None,
        };
        let mut tys = Vec::new();
        if let Some(expected_list) = expected_list {
            for (expr, exp) in exprs.iter().zip(*expected_list) {
                let ty = self.check_expr_with_expectation(expr, Expectation::Guide(*exp));
                tys.push(ty);
            }
        } else {
            for expr in exprs {
                let ty = self.check_expr_with_expectation(expr, Expectation::None);
                tys.push(ty);
            }
        }
        Ty::new_tuple(self.tcx, self.tcx.arena.alloc(tys))
    }

    fn check_expr_literal(&mut self, literal: &'tcx ast::Literal, expected: Option<Ty<'tcx>>, span: Span) -> Ty<'tcx> {
        match literal {
            ast::Literal::String(..) => 
                self.tcx.basic_types.string,
            ast::Literal::Boolean(..) =>
                self.tcx.basic_types.bool,
            ast::Literal::Char(..) =>
                self.tcx.basic_types.char,
            ast::Literal::Integer(int) =>
                self.check_expr_integer(*int, expected, span),
            ast::Literal::Floating(..) => todo!(),
            ast::Literal::Null => {
                let Some(expected) = expected else {
                    Message::error("can't infer type of anonymous null")
                        .at(span)
                        .push(self.diagnostics());
                    return Ty::new_error(self.tcx);
                };
                let Ty(type_ir::TyKind::Never | type_ir::TyKind::Err | type_ir::TyKind::Refrence(..)) = expected else {
                    Message::error(format!("non refrence-type {expected} cannot be null"))
                        .at(span)
                        .push(self.diagnostics());
                    return expected
                };
                expected
            }
        }
    }

    fn check_expr(&mut self, expr: &'tcx ast::Expr, expected: Option<Ty<'tcx>>, is_body: bool) -> Ty<'tcx> {
        match &expr.kind {
            ast::ExprKind::Literal(literal) =>
                self.check_expr_literal(literal, expected, expr.span),
            ast::ExprKind::BinaryOp(binop) =>
                self.check_expr_binop(binop, expr.span, expected),
            ast::ExprKind::AssignOp(assign) =>
                self.check_expr_assignop(assign, expected),
            ast::ExprKind::UnaryOp(unary) => 
                self.check_expr_unary(unary, expected),
            ast::ExprKind::Deref(base) => {
                let expectation = match expected {
                    Some(ty) => Expectation::Guide(Ty::new_refrence(self.tcx, ty)),
                    _ => Expectation::None
                };
                let ty = self.check_expr_with_expectation(base, expectation);
                self.deref(ty, expr.span)
            }
            ast::ExprKind::Path(path) => self.lower_path(path, ResolutionKind::Value),
            ast::ExprKind::Block(block) => {
                if !is_body {
                    let (ctxt, ty) = self.enter_block_ctxt(expr.node_id, |this| {
                        this.check_block(block, Expectation::None)
                    });

                    if let Some(result_ty) = ctxt.result_ty {
                        self.maybe_emit_type_error(ty, result_ty, expr.span);
                        self.diverges.set(Diverges::Maybe);
                        result_ty
                    } else {
                        ty
                    }
                } else {
                    self.check_block(block, expected.into())
                }
            },
            ast::ExprKind::Err =>
                Ty::new_error(self.tcx),
            ast::ExprKind::FunctionCall(call) =>
                self.check_expr_call(call, expr.span),
            ast::ExprKind::Subscript(subscript) =>
                self.check_expr_subscript(subscript),
            ast::ExprKind::Field(field) =>
                self.check_expr_field(field, expr.node_id),
            ast::ExprKind::TypeInit(ty_init) =>
                self.check_expr_init(ty_init, expr.span),
            ast::ExprKind::Cast(cast) =>
                self.check_expr_cast(cast, expected, expr.span),
            ast::ExprKind::Range(range) => {
                {
                    let mut start = &range.start;
                    let mut end = &range.end;
                    if !self.check_expr_ty_definite(&start.kind) && self.check_expr_ty_definite(&end.kind) {
                        (start, end) = (end, start);
                    }

                    let expectation = Expectation::Guide(self.tcx.basic_types.nuint);
                    let start_ty = self.check_expr_with_expectation(start, expectation);
                    self.check_expr_with_expectation(end, Expectation::Guide(start_ty));
                }
                use type_ir::TyKind::{Never, Err, Int};

                let start_ty = self.associations[&range.start.node_id];
                let end_ty = self.associations[&range.end.node_id];
                let mut has_error = false;
                if start_ty != end_ty {
                    self.maybe_emit_type_error(end_ty, start_ty, expr.span);
                    has_error = true;
                }
                if !matches!(start_ty, Ty(Never | Err | Int(..))) {
                    Message::error(format!("type {start_ty} is not steppable"))
                        .at(range.start.span)
                        .push(self.diagnostics());
                    has_error = true;
                }
                if !matches!(end_ty, Ty(Never | Err | Int(..))) {
                    Message::error(format!("type {end_ty} is not steppable"))
                        .at(range.end.span)
                        .push(self.diagnostics());
                    has_error = true;
                }
                if has_error {
                    return Ty::new_error(self.tcx);
                }
                Ty::new_range(self.tcx, start_ty, range.inclusive)
            }
            ast::ExprKind::Tuple(exprs) =>
                self.check_expr_tuple(*exprs, expected),
        }
    }

    fn check_expr_with_expectation(&mut self, expr: &'tcx ast::Expr, expectation: Expectation<'tcx>) -> Ty<'tcx> {
        let expected = match expectation {
            Expectation::None => None,
            Expectation::Guide(ty) | Expectation::Coerce(ty) => Some(ty)
        };

        let prev_diverge = self.diverges.get();
        self.diverges.set(Diverges::Maybe);
        let ty = self.check_expr(expr, expected, false); 

        if let Expectation::Coerce(expected) = expectation {
            self.maybe_emit_type_error(ty, expected, expr.span);
        }

        self.maybe_warn_unreachable(expr.span, "expression");

        if let Ty(type_ir::TyKind::Never) = ty {
            self.diverges.set(std::cmp::max(self.diverges.get(), Diverges::Always(expr.span)));
        }

        self.ty_assoc(expr.node_id, ty);

        self.diverges.set(std::cmp::max(self.diverges.get(), prev_diverge));

        ty
    }

    fn check_return_ty(&mut self, expr: &'tcx ast::Expr, ret_ty: Ty<'tcx>, ret_ty_span: Span) {
        self.return_ty = Some(ret_ty);

        let ty = self.check_expr(&expr, Some(ret_ty), true);
        self.maybe_emit_type_error(ty, ret_ty, ret_ty_span);

        if let Ty(type_ir::TyKind::Void) = ret_ty && let Ty(type_ir::TyKind::Never) = ty {
            Message::warning("unnecessarry return in void function")
                .at(expr.span)
                .push(self.diagnostics());
        }

        self.ty_assoc(expr.node_id, ty); 
    }

    fn maybe_warn_unreachable(&self, span: Span, what: &'static str) {
        if let Diverges::Always(span2) = self.diverges.get() {
            Message::warning(format!("unreachable {what}"))
                .at(span)
                .hint("any code following this expression is unreachable", span2)
                .push(self.diagnostics());
            self.diverges.set(Diverges::WarnedAlways);
        }
    }

    fn maybe_emit_type_error(&self, found: Ty<'tcx>, expected: Ty<'tcx>, span: Span) -> Ty<'tcx> {
        if found != expected {
            Message::error(format!("mismatched types: expected {expected}, found {found}"))
                .at(span)
                .push(self.diagnostics());
            let err = Ty::new_error(self.tcx);
            self.last_error.set(Some(()));
            return err;
        }
        Ty::with_non_bendable(&[found, expected]).unwrap()
    }
    
    fn results(self) -> TypecheckResults<'tcx> {
        TypecheckResults {
            field_indices: self.field_indices,
            associations: self.lowering_ctxt.associations,
            locals: self.lowering_ctxt.locals,
            has_errors: self.lowering_ctxt.last_error.get().is_some()
        }
    }
}

impl<'tcx> std::ops::Deref for TypecheckCtxt<'tcx> {
    type Target = LoweringCtxt<'tcx>;

    fn deref(&self) -> &Self::Target {
        &self.lowering_ctxt
    }
}

impl<'tcx> std::ops::DerefMut for TypecheckCtxt<'tcx> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.lowering_ctxt
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LoweringMode {
    Body, Unbound
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ResolutionKind {
    Type, Value
}

impl std::fmt::Display for ResolutionKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ResolutionKind::Type => f.write_str("type"),
            ResolutionKind::Value => f.write_str("value"),
        }
    }
}

struct LoweringCtxt<'tcx> {
    tcx: TyCtxt<'tcx>,
    lowering_mode: LoweringMode,
    associations: HashMap<ast::NodeId, Ty<'tcx>>,
    locals: HashMap<ast::NodeId, Ty<'tcx>>,
    last_error: Cell<Option<()>>
}

impl<'tcx> LoweringCtxt<'tcx> {
    fn new(tcx: TyCtxt<'tcx>, lowering_mode: LoweringMode) -> Self {
        Self {
            tcx,
            lowering_mode,
            associations: Default::default(),
            locals: Default::default(),
            last_error: Cell::new(None)
        }
    }

    fn diagnostics(&self) -> &DiagnosticsCtxt {
        self.tcx.diagnostics()
    }

    fn ty_assoc(&mut self, node_id: ast::NodeId, ty: Ty<'tcx>) {
        assert_eq!(self.lowering_mode, LoweringMode::Body);
        if let Some(prev) = self.associations.insert(node_id, ty) {
            assert_eq!(ty, prev, "tried to assoicate {node_id:?} twice with different types; First {prev:?} then {ty:?}");
            eprintln!("[WARNING] unwanted attempt to associate {node_id:?} with {ty:?} twice")
        }
        if let Ty(type_ir::TyKind::Err) = ty {
            self.last_error.set(Some(()));
        }
    }

    fn ty_local(&mut self, node_id: NodeId, ty: Ty<'tcx>) {
        assert_eq!(self.lowering_mode, LoweringMode::Body);
        if let Some(prev) = self.locals.insert(node_id, ty) {
            assert_eq!(ty, prev, "tried to create local {node_id:?} twice with different types; First {prev:?} then {ty:?}");
            eprintln!("[WARNING] unwanted attempt to create local {node_id:?} with {ty:?} twice")
        }
        if let Ty(type_ir::TyKind::Err) = ty {
            self.last_error.set(Some(()));
        }
    }

    fn lower_path_in_context(&self, path: &'tcx ast::Path<'tcx>, resolution_kind: ResolutionKind) -> Ty<'tcx> {
        let mut last_resolved_segment = None;
        for (idx, segment) in path.segments.iter().enumerate().rev() {
            if segment.resolution().is_some() {
                last_resolved_segment = Some(idx);
                break;
            }
        }
        let (mut ty, idx) = match last_resolved_segment {
            Some(idx) => {
                let segment = &path.segments[idx];
                let resolution = segment.resolution().unwrap();
                let /*mut*/ ty = self.ty_from_resolution(resolution, ResolutionKind::Type, path.segments[idx].span);
                if segment.generic_args.len() > 0 {
                    todo!("ty = ty.instantciate(generic_args)");
                }
                (ty, idx)
            },
            None => {
                if path.segments[0].ident.is_some() {
                    for seg in path.segments {
                        println!(" -- {} {}", seg.ident.unwrap().symbol, seg.resolution().is_some());
                    }
                    panic!("invalid unresolved path in `lower_path_in_context`");
                }
                let garg = &path.segments[0].generic_args[0];
                let ty = match garg.kind {
                    ast::GenericArgumentKind::Ty(ty) => self.lower_ty(ty),
                    _ => unreachable!()
                };
                (ty, 0)
            }
        };
        if let Ty(TyKind::Err) = ty {
            return ty;
        }

        let mut unresolved_segments = path.segments[idx + 1..].iter();
        let mut current_resolution = ResolutionKind::Type;
        let mut prev = ast::Ident { symbol: sym::int, span: Span::NULL };

        while let Some(segment) = unresolved_segments.next() {
            let ident = segment.ident.unwrap();
            if segment.generic_args.len() > 0 {
                todo!("ty.instanciate(generic_args)");
            }
            prev = ident;
            match ty {
                Ty(TyKind::Enum(enm)) => {    
                    let mut variant = None;
                    for variant_id in &enm.variants {
                        let (_, variant_def) = self.tcx.enum_variant(*variant_id);
                        if variant_def.symbol == ident.symbol {
                            variant = Some(variant_def);
                        }
                    }

                    if let Some(variant) = variant {
                        segment.resolve(ast::Resolution::Def(variant.def, DefinitionKind::Variant));
                    } else {
                        Message::error(format!("can't find variant `{}` on enum `{ty}`", ident.symbol))
                            .at(ident.span)
                            .push(self.diagnostics());
                        segment.resolve(ast::Resolution::Err);
                        self.last_error.set(Some(()));
                    }

                    current_resolution = ResolutionKind::Value;
                    break;
                },
                _ => {
                    current_resolution = resolution_kind;
                    ty = Ty::new_error(self.tcx);
                    path.segments.last().unwrap().resolve(ast::Resolution::Err);
                    break;
                }
            }
        }

        if current_resolution == ResolutionKind::Value && unresolved_segments.next().is_some() {
            Message::error(format!("expected type or module, but `{}` is already value", prev.symbol))
                .at(prev.span)
                .push(self.diagnostics()); 
            path.segments.last().unwrap().resolve(ast::Resolution::Err);
            return Ty::new_error(self.tcx);
        }

        if current_resolution != resolution_kind {
            Message::error(format!("expected {resolution_kind}-like, but found {current_resolution}-like"))
                .at(prev.span)
                .push(self.diagnostics());
            path.segments.last().unwrap().resolve(ast::Resolution::Err);
            return Ty::new_error(self.tcx);
        }

        ty
    }

    fn ty_from_resolution(&self, resolution: &ast::Resolution, resolution_kind: ResolutionKind, span: Span) -> Ty<'tcx> {
        let (ty, resolved_kind) = match resolution {
            ast::Resolution::Local(local) => {
                if self.lowering_mode == LoweringMode::Unbound {
                    panic!("invalid Local Resolution in Unbound LoweringCtxt");
                }
                (self.locals[local], ResolutionKind::Value)
            }
            ast::Resolution::Def(def_id, DefinitionKind::Function | DefinitionKind::Static | DefinitionKind::Const | DefinitionKind::ParamConst) =>
                (self.tcx.type_of(*def_id), ResolutionKind::Value),
            ast::Resolution::Def(def_id, DefinitionKind::Struct | DefinitionKind::Enum | DefinitionKind::ParamTy | DefinitionKind::TypeAlias) =>
                (self.tcx.type_of(*def_id), ResolutionKind::Type),
            ast::Resolution::Primitive(sym) => {
                if *sym == sym::tuple {
                    (Ty::new_tuple(self.tcx, &[]), ResolutionKind::Type)
                } else {
                    (sym.get_primitive_ty(self.tcx).unwrap(), ResolutionKind::Type)
                }
            }
            ast::Resolution::Err =>
                return Ty::new_error(self.tcx),
            ast::Resolution::Def(_, _) => panic!("invalid resolution for path"),
        };

        if resolved_kind != resolution_kind {
            Message::error(format!("expected {resolution_kind}-like, but found {resolved_kind}-like"))
                .at(span)
                .push(self.diagnostics());
            return Ty::new_error(self.tcx);
        }

        ty
    }

    fn lower_path(
        &self,
        path: &'tcx ast::Path<'tcx>,
        resolution_kind: ResolutionKind
    ) -> Ty<'tcx> {
        // TODO: this is comparable to a path resolution at typecheck stage now
        
        let ty = if let Some(resolution) = path.resolution() {
            self.ty_from_resolution(resolution, resolution_kind, path.segments.last().unwrap().span)
        } else {
            self.lower_path_in_context(path, resolution_kind)
        };

        ty
    }

    fn lower_ty(&self, ty: &'tcx ast::TypeExpr<'tcx>) -> Ty<'tcx> {
        match &ty.kind {
            ast::TypeExprKind::Path(path) =>  self.lower_path(path, ResolutionKind::Type),
            ast::TypeExprKind::Ref(ty) => {
                let ty = self.lower_ty(ty);
                Ty::new_refrence(self.tcx, ty)
            },
            ast::TypeExprKind::Array(array) => {
                match array.cap {
                    ast::ArrayCapacity::Discrete(..) | ast::ArrayCapacity::Infer => {
                        let ty = self.lower_ty(array.ty);
                        if let Ty(type_ir::TyKind::Err) = ty {
                            return ty;
                        }

                        let cap = if let ast::ArrayCapacity::Discrete(expr) = &array.cap {
                            type_ir::Const::from_definition(self.tcx, *expr.def_id.get().unwrap())
                        } else {
                            self.tcx.intern_const(ConstKind::Infer)
                        };

                        if let type_ir::Const(type_ir::ConstKind::Err) = &cap {
                            return Ty::new_error(self.tcx);
                        }

                        Ty::new_array(self.tcx, ty, cap)
                    },
                    ast::ArrayCapacity::Dynamic => {
                        let ty = self.lower_ty(array.ty);
                        Ty::new_dyn_array(self.tcx, ty)
                    }
                }
            }
            ast::TypeExprKind::Slice(ty) => {
                let ty = self.lower_ty(ty);
                if let Ty(type_ir::TyKind::Err) = ty {
                    return ty;
                }
                Ty::new_slice(self.tcx, ty)
            }
            ast::TypeExprKind::Err => Ty::new_error(self.tcx)
        }
    }
}

pub fn type_of(tcx: TyCtxt<'_>, def_id: DefId) -> Ty<'_> {
    let node = tcx.node_by_def_id(def_id);

    match node {
        ast::Node::Item(item) => match &item.kind {
            ast::ItemKind::Function(_) =>
                Ty::new_function(tcx, def_id),
            ast::ItemKind::Enum(enm) => {
                let mut representation = None;
                if let Some(repr) = enm.representation {
                    let ctxt = LoweringCtxt::new(tcx, LoweringMode::Unbound);
                    let ty = ctxt.lower_ty(repr);
                    if !matches!(ty, Ty(TyKind::Int(..) | TyKind::Char)) {
                        Message::error(format!("representation for enum `{}` is not allowed to be of type {ty}", enm.ident.symbol))
                            .at(repr.span)
                            .note("allowed types are char and {integers}")
                            .push(tcx.diagnostics());
                        representation = Some(Ty::new_error(tcx));
                    } else {
                        representation = Some(ty);
                    }
                }

                let variants = enm.variants
                    .iter()
                    .map(|v| *v.def_id.get().unwrap())
                    .collect::<Vec<_>>();

                Ty::new_enum(tcx, type_ir::Enum::new(def_id, enm.ident.symbol, representation, variants))
            }
            ast::ItemKind::Struct(stc) => {
                let fields = stc.fields.iter().map(|fdef| {
                    let def_id = *fdef.def_id.get().unwrap();
                    type_ir::FieldDef { def: def_id, symbol: fdef.name.symbol }
                }).collect();
                let adt_def = tcx.intern_adt(AdtKind::Struct(type_ir::Struct::new(def_id, stc.ident.symbol, fields)));
                Ty::new_adt(tcx, adt_def)
            },
            ast::ItemKind::GlobalVar(global) => {
                if let Some(ty) = global.ty {
                    let ctxt = LoweringCtxt::new(tcx, LoweringMode::Unbound);
                    return ctxt.lower_ty(ty);
                }
                todo!("ty-class global consts")
            },
            ast::ItemKind::Import(_) => panic!("resolved Import to Definition"),
            ast::ItemKind::Alias(alias) if let ast::AliasKind::Type(ty) = alias.kind => {
                let ctxt = LoweringCtxt::new(tcx, LoweringMode::Unbound);
                ctxt.lower_ty(ty)
            },
            ast::ItemKind::Alias(alias) => panic!("resolved AliasKind {:?} to Definition", alias.kind),
            ast::ItemKind::Err => panic!("resolved Err to Definiton")
        }
        ast::Node::GenericParam(param) => {
            match param.kind {
                ast::GenericParamKind::Type(ty) => {
                    let owner_node = tcx.owner_node(param.node_id);

                    let generics = owner_node.generics();
                    let index = generics
                        .iter()
                        .position(|p| p.node_id == param.node_id)
                        .expect("`param` should be a generic param on its owner");

                    Ty::new_param(tcx, ty.symbol, index)
                }
                ast::GenericParamKind::Const(..) => todo!()
            }
        }
        ast::Node::FieldDef(field) => {
            let ctx = LoweringCtxt::new(tcx, LoweringMode::Unbound);
            ctx.lower_ty(&field.ty)
        }
        ast::Node::Variant(..) => tcx.enum_variant(def_id).0,
        ast::Node::NestedConst(nested) => {
            let parent_node_id = tcx.parent_of(nested.node_id);
            let parent_node = tcx.get_node_by_id(parent_node_id);
            match parent_node {
                ast::Node::TypeExpr(ty) if let ast::TypeExprKind::Array(_) = ty.kind =>
                    tcx.basic_types.nuint,
                ast::Node::TypeExpr(ast::TypeExpr { kind: ast::TypeExprKind::Path(_path), .. })
                    | ast::Node::Expr(ast::Expr { kind: ast::ExprKind::Path(_path), .. }) =>
                    todo!("resolve path partially"),
                ast::Node::Item(ast::Item { kind: ast::ItemKind::Function(ast::Function { member_path: Some(_path), .. }), .. }) =>
                    todo!("resolve path partially"),
                ast::Node::Variant(_) => {
                    let enum_node_id = tcx.parent_of(parent_node.node_id());
                    let ast::Node::Item(item @ ast::Item { kind: ast::ItemKind::Enum(..), .. }) = tcx.get_node_by_id(enum_node_id) else {
                        unreachable!("parent of Variant must be Enum")
                    };

                    let ty = tcx.type_of(*item.def_id.get().unwrap());

                    let Ty(TyKind::Enum(enm)) = ty else {
                        unreachable!("")
                    };

                    // FIXME: Use unknown int-type here (e.g. {integer}). Important is just to know
                    // that this is an integer (or char alternatively) when trying to evaluate the
                    // const and that the user-chosen signedness, not the exact size in case we
                    // stil need to calculate
                    enm.representation.unwrap_or(tcx.basic_types.long)
                }
                _ => unreachable!("TODO: ast::Node::Item()")
            }
        }
        _ => panic!("only items can be declarations")
    }
}

pub struct TypecheckResults<'tcx> {
    pub field_indices: HashMap<ast::NodeId, type_ir::FieldIdx>,
    pub associations: HashMap<ast::NodeId, Ty<'tcx>>,
    pub locals: HashMap<ast::NodeId, Ty<'tcx>>,
    pub has_errors: bool
}

pub fn typecheck(tcx: TyCtxt<'_>, def_id: DefId) -> &'_ TypecheckResults<'_> {
    let node = tcx.node_by_def_id(def_id);

    let body = node.body()
        .expect("typecheck on node without a body");

    let mut ctxt = TypecheckCtxt::new(tcx);

    if let Some(ast::FnSignature { returns, .. }) = node.signature() {
        let sig = tcx.fn_sig(def_id);
        for param in sig.params {
            ctxt.ty_local(param.node_id, param.ty);
        }
        ctxt.check_return_ty(body.body, sig.returns, returns.span);
    } else {
        let ty = tcx.type_of(def_id);
        ctxt.check_expr_with_expectation(body.body, Expectation::Coerce(ty));
    }

    tcx.arena.alloc(ctxt.results())
}

fn check_valid_intrinsic(
    ident: ast::Ident,
    params: &[type_ir::Param],
    result_ty: Ty,
    tcx: TyCtxt
) -> bool {
    let name = ident.symbol;

    let closure = || {
        macro_rules! early {
            ($expr:expr) => {
                if !$expr {
                    return Ok(false);
                }
            };
        }
        let mut params = params.iter();
        macro_rules! param {
            () => { params.next().map(|p| p.ty) };
        }
        match name {
            sym::main => {
                early!(matches!(param!(), Some(Ty(TyKind::Slice(Ty(TyKind::String))))));
                early!(matches!(param!(), None));
                early!(matches!(result_ty, Ty(TyKind::Int(type_ir::Integer::I32, true))));
            }
            sym::stringdata => {
                early!(matches!(param!(), Some(Ty(TyKind::String))));
                early!(matches!(param!(), None));
                early!(matches!(result_ty, Ty(TyKind::Refrence(Ty(TyKind::Int(type_ir::Integer::I8, false))))));
            }
            sym::stringlen => {
                early!(matches!(param!(), Some(Ty(TyKind::String))));
                early!(matches!(param!(), None));
                early!(matches!(result_ty, Ty(TyKind::Int(type_ir::Integer::ISize, false))));
            }
            sym::slice_to_raw_parts => {
                early!(matches!(param!(), Some(Ty(TyKind::Slice(Ty(TyKind::Param(type_ir::ParamTy { index: 0, .. })))))));
                early!(matches!(param!(), None));
                let Ty(TyKind::Tuple(tuple)) = result_ty else {
                    return Ok(false);
                };
                println!("return ty is a tuple");
                let mut tuple = tuple.iter();
                early!(matches!(tuple.next(), Some(Ty(TyKind::Refrence(Ty(TyKind::Param(type_ir::ParamTy { index: 0, .. })))))));
                println!("tuple.0 is T*");
                early!(matches!(tuple.next(), Some(Ty(TyKind::Int(type_ir::Integer::ISize, false)))));
                println!("tuple.1 is nuint");
                early!(matches!(tuple.next(), None));
                println!("tuple len == 2");
            }
            sym::string_from_raw_parts => {
                early!(matches!(param!(), Some(Ty(TyKind::Refrence(Ty(TyKind::Int(type_ir::Integer::I8, false)))))));
                early!(matches!(param!(), Some(Ty(TyKind::Int(type_ir::Integer::ISize, false)))));
                early!(matches!(param!(), None));
                early!(matches!(result_ty, Ty(TyKind::String)));
            }
            _ => {
                Message::error(format!("function `{name}` is not a known compiler intrinsic"))
                    .at(ident.span)
                    .push(tcx.diagnostics());
                return Err(());
            }
        }

        Ok(true)
    };

    if let Ok(false) = closure() {
        Message::error(format!("intrinsic `{name}` doesn't match the expected signature"))
            .at(ident.span)
            .push(tcx.diagnostics());
        return false;
    }

    true
}

pub fn enum_variant<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> (Ty<'tcx>, &'tcx type_ir::VariantDef<'tcx>) {
    let node = tcx.node_by_def_id(def_id);
    let ast::Node::Variant(variant) = node else {
        panic!("non-variant definition in enum_variant")
    };

    let parent_node_id = tcx.parent_of(node.node_id());
    let parent_node = tcx.get_node_by_id(parent_node_id);

    let ast::Node::Item(enm @ ast::Item { kind: ast::ItemKind::Enum(_), .. }) = parent_node else {
        panic!("non-enum owner for variant def")
    };

    let ty = tcx.type_of(*enm.def_id.get().unwrap());

    let def_id = *variant.def_id.get().unwrap();
    let discriminant = variant
        .discriminant
        .map(|cnst| type_ir::Const::from_definition(tcx, *cnst.def_id.get().unwrap()))
        .map(|cnst| type_ir::VariantDescriminant::Uncalculated(cnst))
        .unwrap_or_default();
    let variant = tcx.arena.alloc(type_ir::VariantDef {
        def: def_id,
        symbol: variant.name.symbol,
        discriminant: Cell::new(discriminant)
    });

    (ty, variant)
}

pub fn fn_sig(tcx: TyCtxt<'_>, def_id: DefId) -> type_ir::Signature {
    let node = tcx.node_by_def_id(def_id);
    let ctxt = LoweringCtxt::new(tcx, LoweringMode::Unbound);

    let ast::Node::Item(ast::Item { kind: ast::ItemKind::Function(func), .. }) = node else {
        panic!("non-function definition in fn_sig")
    };

    let mut returns = ctxt.lower_ty(&func.sig.returns);
    let mut has_errors = false;
    if returns.is_incomplete() {
        Message::error(
            format!("type {returns} is incomplete, incomplete types are not allowed in function signatures"))
            .at(func.sig.returns.span)
            .push(tcx.diagnostics());
        returns = Ty::new_error(tcx);
        has_errors = true;
    }

    let mut params = Vec::new();
    for param in func.sig.params {
        let mut ty = ctxt.lower_ty(&param.ty);
        let name = param.ident.symbol;

        if ty.is_incomplete() {
            Message::error(format!("type {ty} is incomplete, incomplete types are not allowed in function signatures"))
                .at(param.ty.span)
                .push(tcx.diagnostics());
            ty = Ty::new_error(tcx);
            has_errors = true;
        }


        params.push(type_ir::Param {
            name,
            ty,
            node_id: param.node_id
        });
    }

    let params: Box<[type_ir::Param]> = params.into_boxed_slice();
    let params: &'_ [type_ir::Param] = tcx.arena.alloc(params);

    let header = &func.sig.header;
    if func.body.is_none() && header.link.is_none() && header.compiler_intrinsic.is_none() {
        Message::warning(format!("function `{}` doesn't have a body but isn't linked externally either", func.ident.symbol))
            .at(func.span)
            .note("add `#link` directive to signfify external linking")
            .push(tcx.diagnostics());
        has_errors = true;
    }

    if let Some(span) = header.link && header.compiler_intrinsic.is_some() {
        Message::error("cannot specify `#link` and `#compiler_intrinsic` for the same function")
            .at(span)
            .note("remove `#link`")
            .push(tcx.diagnostics());
        has_errors = true;
    }

    if let Some(span) = header.link && func.body.is_some() {
        Message::error("the directive `#link` can only be specified for bodyless functions")
            .at(span)
            .note("remove `#link`")
            .push(tcx.diagnostics());
        has_errors = true;
    }

    if let Some(span) = header.compiler_intrinsic && func.body.is_some() {
        Message::error("the directive `#compiler_intrinsic` can only be specified for bodyless functions")
            .at(span)
            .note("remove `#compiler_intrinsic`")
            .push(tcx.diagnostics());
        has_errors = true;
    }

    match (header.link, header.c_call) {
        (Some(span), Some(_)) if func.body.is_some() => {
            Message::error("cannot specify `#link` and `#c_call` for the same function")
                .at(span)
                .note("remove `#link`, as `#c_call` is enough to make a function C-visible")
                .push(tcx.diagnostics());
            has_errors = true;
        }
        (Some(_), Some(c_call)) if func.body.is_none() => {
            Message::error("cannot specify `#link` and `#c_call` for the same function")
                .at(c_call.span)
                .note("remove `#c_call`, as `#link` is enough to link an external function")
                .push(tcx.diagnostics());
            has_errors = true;
        }
        _ => ()
    }

    if !has_errors && header.compiler_intrinsic.is_some() {
        has_errors |= !check_valid_intrinsic(func.ident, params, returns, tcx);
    }

    type_ir::Signature {
        name: func.ident.symbol,
        params,
        returns,
        has_errors,
        intrinsic: !has_errors && header.compiler_intrinsic.is_some()
    }
}
