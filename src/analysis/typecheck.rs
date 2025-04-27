use std::cell::Cell;

use hashbrown::HashMap;
use num_traits::ToPrimitive;

use crate::{syntax::{ast::{self, DefId, DefinitionKind, NodeId}, lexer::{self, Span}}, context::TyCtxt, diagnostics::{DiagnosticsCtxt, Message}, type_ir::{self, AdtDef, AdtKind, ConstKind, Integer, Ty}};

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
    variant_translations: HashMap<ast::NodeId, type_ir::VariantIdx>,
    lowering_ctxt: LoweringCtxt<'tcx>,
    associations: HashMap<ast::NodeId, Ty<'tcx>>,
    locals: HashMap<ast::NodeId, Ty<'tcx>>,
    last_error: Cell<Option<Ty<'tcx>>>
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
            variant_translations: Default::default(),
            lowering_ctxt: LoweringCtxt::new(tcx),
            associations: Default::default(),
            locals: Default::default(),
            last_error: Cell::new(None)
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

    fn ty_assoc(&mut self, node_id: ast::NodeId, ty: Ty<'tcx>) {
        if let Some(prev) = self.associations.insert(node_id, ty) {
            assert_eq!(ty, prev, "tried to assoicate {node_id:?} twice with different types; First {prev:?} then {ty:?}");
            eprintln!("[WARNING] unwanted attempt to associate {node_id:?} with {ty:?} twice")
        }
        if let Ty(type_ir::TyKind::Err) = ty {
            self.last_error.set(Some(ty));
        }
    }

    fn ty_local(&mut self, node_id: NodeId, ty: Ty<'tcx>) {
        if let Some(prev) = self.locals.insert(node_id, ty) {
            assert_eq!(ty, prev, "tried to create local {node_id:?} twice with different types; First {prev:?} then {ty:?}");
            eprintln!("[WARNING] unwanted attempt to create local {node_id:?} with {ty:?} twice")
        }
        if let Ty(type_ir::TyKind::Err) = ty {
            self.last_error.set(Some(ty));
        }
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
        let expected = local.ty.map(|ty| self.lowering_ctxt.lower_ty(&ty));

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
            self.ty_local(stmt.node_id, Ty::new_error(self.tcx));
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
                Integer::fit_signed((int.value as i128) * if int.signed { -1 } else { 1 }).map_or(128, |i| i.size(&self.tcx))
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
            // ast::ExprKind::ShorthandEnum(..) => false,
            ast::ExprKind::Block(_) => true, // block is to complicated, so it's going to be matched
            ast::ExprKind::FunctionCall(..) | ast::ExprKind::TypeInit(..) |
            ast::ExprKind::Subscript(..) | ast::ExprKind::Field(..) |
            ast::ExprKind::Name(..) | ast::ExprKind::Deref(..) |
            ast::ExprKind::Literal(..) | ast::ExprKind::Err => true,
        }
    }

    fn check_op_between(&self, op: lexer::BinaryOp, lhs: Ty<'tcx>, rhs: Ty<'tcx>) -> Option<Ty<'tcx>> {
        macro_rules! boolop {
            ($ret:expr) => {{
                use lexer::BinaryOp::*;
                if let GreaterThan | GreaterEqual | LessThan | LessEqual = op {
                    return Some(self.tcx.basic_types.bool);
                }
                return Some($ret);
            }};
        }

        {
            use lexer::BinaryOp::*;
            let (Plus | Minus | Mul | Div | Mod |
                 LeftShift | RightShift | BitwiseAnd | BitwiseOr | BitwiseXor |
                 GreaterThan | GreaterEqual | LessThan | LessEqual) = op else {
                panic!("check_op_between used on invalid operator {op:?}");
            };
        }
        fn get_int(ty: Ty<'_>) -> Option<Ty<'_>> {
            match ty { 
                Ty(type_ir::TyKind::Int(..)) => Some(ty),
                _ => None,
            }
        }

        if let Some(bendable) = Ty::with_bendable(&[lhs, rhs]) {
            return Some(bendable);
        }

        let Some((lhs_int, rhs_int)) = Option::zip(get_int(lhs), get_int(rhs)) else {
            return None;
        };

        // Simple case
        if lhs_int == rhs_int {
            boolop!(lhs_int);
        }

        return None;
    }

    fn check_expr_assignop(&mut self, assign: &'tcx ast::AssignOp<'tcx>, expected: Option<Ty<'tcx>>) -> Ty<'tcx> {
        let is_valid_lhs = {
            use ast::ExprKind::{Subscript, Field, Name, Deref};
            matches!(assign.lhs.kind, Subscript(..) | Field(..) | Name(..) | Deref(..)) 
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
        let base = {
            use type_ir::TyKind::{Err, Never, Array, DynamicArray, Slice};
            if let Ty(Err | Never) = ty {
                return ty;
            }
            let Ty(Array(base, _) | DynamicArray(base) | Slice(base)) = ty else {
                Message::error(format!("cannot index into value of type {ty}"))
                    .at(index_span)
                    .push(self.diagnostics());
                return Ty::new_error(self.tcx);
            };

            *base
        };

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
        let ty = self.lowering_ctxt.lower_ty(ty_init.ty);
        
        use type_ir::TyKind::{self, Int, Float, Char, Bool, Void, String};
        match ty {
            Ty(Int(..) | Float(..) | Char | Bool | Void | String) => {
                Message::error(format!("expected struct, found primitive {ty}"))
                    .at(span)
                    .note("initialze primitive directly")
                    .push(self.diagnostics());
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
            }
            Ty(TyKind::Tuple(..)) => {
                Message::error(format!("expected struct, found tuple {ty}"))
                    .at(span)
                    .note("initialize tuple using tuple expression (<0>, <1>, ...)")
                    .push(self.diagnostics());
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
                        }
                    }
                    _ => ()
                }
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
                            ast::TypeInitKind::Direct(expr) if let ast::ExprKind::Name(name) = &expr.kind => {
                                let Some((idx, fdef)) = fields.get(&name.ident.symbol) else {
                                    Message::error(format!("can't find field `{}` on struct {ty}", name.ident.symbol.get()))
                                        .at(name.ident.span)
                                        .push(self.diagnostics());
                                    continue;
                                };
                                let fty = self.tcx.type_of(fdef.def);
                                self.check_expr_with_expectation(expr, Expectation::Coerce(fty));
                                self.field_indices.insert(expr.node_id, *idx);
                            }
                            ast::TypeInitKind::Direct(expr) => {
                                Message::error("immediate initializer in struct initialization is invalid")
                                    .at(expr.span)
                                    .push(self.diagnostics());
                            }
                        }
                    }
                }
                AdtDef(type_ir::AdtKind::Enum(..)) => {
                    Message::error(format!("expected struct, found enum {ty}"))
                        .at(span)
                        .note(format!("initialize an enum with {}::<Variant> syntax", adt.name().get()))
                        .push(self.diagnostics());
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
        use type_ir::TyKind::{Err, Never, Int, Float, Char, Bool};
        if let Ty(Err | Never) = from {
            return true;
        }
        if let Ty(Err | Never) = to {
            return true;
        }

        if let (Ty(Int(..) | Float(..)), Ty(Int(..) | Float(..))) = (to, from) {
            return true;
        } 

        // int <-> bool conversions +
        // u32 <-> char conversions
        return match (from, to) {
            (Ty(Int(..)), Ty(Bool)) => true,
            (Ty(Bool), Ty(Int(..))) => true,

            (Ty(Int(Integer::I32, false)), Ty(Char)) => true,
            (Ty(Char), Ty(Int(Integer::I32, false))) => true,
            _ => false
        };
    }

    fn check_expr_cast(&mut self, cast: &'tcx ast::Cast<'tcx>, expected: Option<Ty<'tcx>>, span: Span) -> Ty<'tcx> {

        let ty = cast.ty.map(|expr| self.lowering_ctxt.lower_ty(expr));
        
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
            ast::ExprKind::Name(name) =>
                self.check_expr_name(name),
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

    fn check_expr_name(&mut self, name: &ast::Name) -> Ty<'tcx> {
        let Some(resolution) = name.resolution() else {
            panic!("unresolved Name in check_expr_name(...)");
        };
        match resolution {
            ast::Resolution::Local(node_id) => 
                *self.locals.get(node_id)
                    .expect("check_expr_name(...) unknown Local(NodeId)"),
            ast::Resolution::Def(def_id, DefinitionKind::Function | DefinitionKind::Const | DefinitionKind::Static) =>
                self.tcx.type_of(*def_id),
            ast::Resolution::Err => Ty::new_error(self.tcx),
            ast::Resolution::Primitive |
            ast::Resolution::Def(_, DefinitionKind::Enum | DefinitionKind::Struct) => 
                panic!("type-like resolution in check_expr_name"),
            ast::Resolution::Def(_, DefinitionKind::NestedConst | DefinitionKind::Variant | DefinitionKind::Field) => 
                panic!("nested definition in check_expr_name"),
        }
    }

    fn check_expr_with_expectation(&mut self, expr: &'tcx ast::Expr, expectation: Expectation<'tcx>) -> Ty<'tcx> {
        let expected = match expectation {
            Expectation::None => None,
            Expectation::Guide(ty) | Expectation::Coerce(ty) => Some(ty)
        };

        let prev_diverge = self.diverges.get();
        self.diverges.set(Diverges::Maybe);
        let ty = self.check_expr(&expr, expected, false); 

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
            return Ty::new_error(self.tcx);
        }
        Ty::with_non_bendable(&[found, expected]).unwrap()
    }
    
    fn results(self) -> TypecheckResults<'tcx> {
        TypecheckResults {
            field_indices: self.field_indices,
            variant_translations: self.variant_translations,
            associations: self.associations,
            locals: self.locals,
            has_errors: self.last_error.get().is_some()
        }
    }
}

struct LoweringCtxt<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> LoweringCtxt<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
        }
    }

    fn diagnostics(&self) -> &DiagnosticsCtxt {
        self.tcx.diagnostics()
    }

    fn lower_name(&self, name: &ast::Name) -> Ty<'tcx> {
        let Some(resolution) = name.resolution() else {
            panic!("unresolved Name in lower_name(...)");
        };
        match resolution {
            ast::Resolution::Primitive => {
               name.ident.symbol.get_primitive_ty(self.tcx)
                   .expect("non-primitive Ident for primitive name resolution")
            }
            ast::Resolution::Def(def_id, DefinitionKind::Enum | DefinitionKind::Struct) =>
                self.tcx.type_of(*def_id),
            ast::Resolution::Err => Ty::new_error(self.tcx),
            _ => panic!("unexpected Resolution in lower_name")
        }
    }

    fn lower_ty(&self, ty: &ast::TypeExpr) -> Ty<'tcx> {
        match &ty.kind {
            ast::TypeExprKind::Name(name) => 
                self.lower_name(name),
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
                        let ty = self.lower_ty(ty);
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
            ast::TypeExprKind::Generic(..) => panic!("lowering generic types is not supported yet"),
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
                let variants = enm.variants.iter().map(|variant| {
                    let def_id = *variant.def_id.get().unwrap();
                    type_ir::VariantDef { def: def_id, symbol: variant.name.symbol }
                }).collect();
                let adt_def = tcx.intern_adt(AdtKind::Enum(type_ir::Enum::new(def_id, enm.ident.symbol, variants)));
                Ty::new_adt(tcx, adt_def)
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
                let ctxt = LoweringCtxt::new(tcx);
                ctxt.lower_ty(global.ty)
            },
            ast::ItemKind::Err =>
                panic!("resolved Err to Definiton")
        }
        ast::Node::FieldDef(field) => {
            let ctx = LoweringCtxt::new(tcx);
            ctx.lower_ty(&field.ty)
        }
        ast::Node::NestedConst(_nested) => {
            // FIXME: GenericArgs aren't supported at all currently,
            // making the only other place for a NestedConst ArrayCap,
            // which is always nuint
            tcx.basic_types.nuint
        }
        _ => panic!("only items can be declarations")
    }
}

pub struct TypecheckResults<'tcx> {
    pub field_indices: HashMap<ast::NodeId, type_ir::FieldIdx>,
    pub variant_translations: HashMap<ast::NodeId, type_ir::VariantIdx>,
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

pub fn fn_sig(tcx: TyCtxt<'_>, def_id: DefId) -> type_ir::Signature {
    let node = tcx.node_by_def_id(def_id);
    let ctxt = LoweringCtxt::new(tcx);

    match node {
        ast::Node::Item(ast::Item { kind: ast::ItemKind::Function(func), .. }) => {
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

            type_ir::Signature {
                name: func.ident.symbol,
                params,
                returns,
                has_errors
            }
        }
        _ => {
            panic!("non-function definition in fn_sig")
        }
    }
}
