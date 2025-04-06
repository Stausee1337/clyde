use core::panic;
use std::{collections::HashMap, cell::Cell};

use crate::{context::TyCtxt, types::{Ty, ConstInner, Primitive, NumberSign, self}, ast::{DefId, self, DefinitionKind, TypeExpr, NodeId}, diagnostics::{DiagnosticsCtxt, Message}, lexer::{self, Span}};

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

struct TypecheckCtxt<'tcx> {
    tcx: TyCtxt<'tcx>,
    return_ty: Option<Ty<'tcx>>,
    diverges: Cell<Diverges>,
    loop_stack: Vec<LoopCtxt>,
    field_indices: HashMap<ast::NodeId, types::FieldIdx, ahash::RandomState>,
    variant_translations: HashMap<ast::NodeId, types::FieldIdx, ahash::RandomState>,
    lowering_ctxt: LoweringCtxt<'tcx>,
    associations: HashMap<ast::NodeId, Ty<'tcx>, ahash::RandomState>,
}

impl<'tcx> TypecheckCtxt<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            return_ty: None,
            diverges: Cell::new(Diverges::Maybe),
            loop_stack: Vec::new(),
            field_indices: Default::default(),
            variant_translations: Default::default(),
            lowering_ctxt: LoweringCtxt::new(tcx),
            associations: Default::default()
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

    fn ty_assoc(&mut self, node_id: ast::NodeId, ty: Ty<'tcx>) {
        if let Some(prev) = self.associations.insert(node_id, ty) {
            assert_eq!(ty, prev, "tried to assoicate {node_id:?} twice with different types; First {prev:?} then {ty:?}");
            println!("[WARNING] unwanted attempt to associate {node_id:?} with {ty:?} twice")
        }
    }

    fn autoderef(&self, mut ty: Ty<'tcx>, level: i32) -> Option<Ty<'tcx>> {
        let mut idx = 0;
        while idx != level {
            match ty {
                Ty(types::TyKind::Refrence(base)) => {
                    if idx == level - 1 {
                        return Some(*base);
                    }
                    ty = *base;
                },
                Ty(types::TyKind::Err | types::TyKind::Never) =>
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

    fn check_stmt_assign(&mut self, lhs: &'tcx ast::Expr, rhs: &'tcx ast::Expr) {
        let is_valid_lhs = {
            use ast::ExprKind::{Subscript, Field, Name, Deref};
            matches!(lhs.kind, Subscript(..) | Field(..) | Name(..) | Deref(..)) 
        };
        if !is_valid_lhs {
            Message::error("invalid left hand side in assignment")
                .at(lhs.span)
                .push(self.diagnostics());
        }
        let lhs_ty = self.check_expr_with_expectation(lhs, Expectation::None);
        if let Ty(types::TyKind::Never) = self.check_expr_with_expectation(rhs, Expectation::Coerce(lhs_ty)) {
            self.diverges.set(Diverges::Always(rhs.span));
        }
    }

    fn check_stmt_if(
        &mut self,
        condition: &'tcx ast::Expr, body: &'tcx ast::Block, else_branch: Option<&'tcx ast::Stmt>) -> Ty<'tcx> {
        self.check_expr_with_expectation(
            condition, Expectation::Coerce(Ty::new_primitive(self.tcx, types::Primitive::Bool)));

        self.maybe_warn_unreachable(body.span, "block");

        let cond_diverges = self.diverges.replace(Diverges::Maybe);

        let mut body_ty = self.check_block(body, Expectation::None);
        let body_diverges = self.diverges.replace(Diverges::Maybe);


        if let Some(else_branch) = else_branch {
            let else_ty = self.check_stmt(else_branch);
            let else_diverges = self.diverges.get();

            body_ty = self.maybe_emit_type_error(else_ty, body_ty, else_branch.span);

            self.diverges.set(std::cmp::max(cond_diverges, std::cmp::min(body_diverges, else_diverges)));
        } else {
            self.diverges.set(cond_diverges);
            body_ty = Ty::new_primitive(self.tcx, types::Primitive::Void);
        }

        // self.diverges.set(std::cmp::max(self.diverges.get(), prev_diverge));

        body_ty
    }

    fn check_stmt_while(&mut self,
            condition: &'tcx ast::Expr, body: &'tcx ast::Block) -> Ty<'tcx> {

        let bool = Ty::new_primitive(self.tcx, types::Primitive::Bool);
        let res = self.check_expr_with_expectation(condition, Expectation::Coerce(bool));

        self.maybe_warn_unreachable(body.span, "block");

        let cond_diverges = self.diverges.replace(Diverges::Maybe);

        let mut endless = false;
        // TODO: repace with propper compile time constant evaluation
        if res == bool && matches!(condition.kind, ast::ExprKind::Constant(ast::Constant::Boolean(true))) {
            endless = true;
        }

        let ctxt = LoopCtxt {
            owner: body.node_id, may_break: false
        };

        let void = Ty::new_primitive(self.tcx, types::Primitive::Void);
        let (ctxt, ()) = self.enter_loop_ctxt(ctxt, |this| {
            this.check_block(body, Expectation::Coerce(void));
        });

        if !endless || ctxt.may_break {
            self.diverges.set(std::cmp::max(cond_diverges, Diverges::Maybe));
            return Ty::new_primitive(self.tcx, types::Primitive::Void);
        }

        Ty::new_never(self.tcx)
    }

    fn check_stmt_for(&mut self, iter: &'tcx ast::Expr, body: &'tcx ast::Block, node_id: NodeId) {

        let iter_ty  = self.check_expr_with_expectation(iter, Expectation::None);

        self.maybe_warn_unreachable(body.span, "block");

        let iter_diverges = self.diverges.replace(Diverges::Maybe);

        let base = {
            use types::TyKind::{Never, Err, Slice, Array, DynamicArray, Range, Refrence};

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
                    .at(iter.span)
                    .push(self.diagnostics());
                Ty::new_error(self.tcx)
            }
        };

        self.ty_assoc(node_id, base);

        let ctxt = LoopCtxt {
            owner: body.node_id, may_break: false
        };

        let void = Ty::new_primitive(self.tcx, types::Primitive::Void);
        let (_, ()) = self.enter_loop_ctxt(ctxt, |this| {
            this.check_block(body, Expectation::Coerce(void));
        });

        self.diverges.set(std::cmp::max(iter_diverges, Diverges::Maybe));
    }

    fn check_stmt_local(&mut self,
        stmt: &'tcx ast::Stmt, expr: Option<&'tcx ast::Expr>, ty: Option<&'tcx ast::TypeExpr>) {
        let expected = ty.map(|ty| self.lowering_ctxt.lower_ty(&ty));

        if let Some(expected) = expected {
            if expected.is_incomplete() {
                let span = unsafe { ty.unwrap_unchecked() }.span;
                Message::fatal(format!("type infrence in local variables is not supported"))
                    .at(span)
                    .push(self.diagnostics());
            }
        }

        if expected.is_none() && expr.is_none() {
            Message::error("type-anonymous variable declarations require an init expresssion")
                .at(stmt.span)
                .push(self.diagnostics());
            self.ty_assoc(stmt.node_id, Ty::new_error(self.tcx));
            return;
        } else if let Some(expr) = expr {
            let ty = self.check_expr_with_expectation(expr, expected.into());
            if let Ty(types::TyKind::Never) = ty {
                self.ty_assoc(stmt.node_id, expected.unwrap_or(ty)); 
                // TODO: figure out what really to do with that
                // maybe some sort of a `Bendable` TyKind, for this
                // specific situations. For now its `Never`
                // eg. var test = todo();
                self.diverges.set(Diverges::Always(stmt.span));
                return;
            }
            self.ty_assoc(stmt.node_id, expected.unwrap_or(ty));
        } else if let Some(expected) = expected {
            // TODO: check if TyKind can acutally be instantiated like this:
            // Type var; So to speak, checking if a type is fully defaultable
            self.ty_assoc(stmt.node_id, expected);
        } else {
            unreachable!()
        }
    }

    fn check_stmt(&mut self, stmt: &'tcx ast::Stmt) -> Ty<'tcx> {
        match &stmt.kind {
            ast::StmtKind::Expr(expr) => {
                let ty = self.check_expr_with_expectation(expr, Expectation::None);
                if let Ty(types::TyKind::Never) = ty {
                    return ty;
                }
            }
            ast::StmtKind::Assign(lhs, rhs) =>
                self.check_stmt_assign(lhs, rhs), 
            ast::StmtKind::If(condition, body, branch) =>
                return self.check_stmt_if(condition, body, branch.as_deref()),
            ast::StmtKind::While(condition, body) =>
                return self.check_stmt_while(condition, body),
            ast::StmtKind::For(_, iter, body) =>
                self.check_stmt_for(iter, body, stmt.node_id),
            ast::StmtKind::Local(_, ty, expr) =>
                self.check_stmt_local(stmt, expr.as_deref(), ty.as_deref()),
            ast::StmtKind::Block(block) =>
                return self.check_block(block, Expectation::None),
            ast::StmtKind::Return(expr) => {
                let Some(return_ty) = self.return_ty else {
                    Message::error("`return` found outside of function body")
                        .at(stmt.span)
                        .note("use break ...; for producing values")
                        .push(self.diagnostics());
                    return Ty::new_error(self.tcx);
                };
                let ty = expr
                    .as_ref()
                    .map(|expr| self.check_expr_with_expectation(expr, Expectation::Coerce(return_ty)));
                let ty = match ty {
                    Some(ty) => ty,
                    None => {
                        let ty = Ty::new_primitive(self.tcx, types::Primitive::Void);
                        self.maybe_emit_type_error(ty, return_ty, stmt.span);
                        ty
                    }
                };
                self.ty_assoc(stmt.node_id, ty);
                return Ty::new_never(self.tcx);
            }
            ast::StmtKind::ControlFlow(flow) => {
                if let Ok(owner) = flow.destination {
                    if flow.kind == ast::ControlFlowKind::Break {
                        let ctxt = self.loop_ctxt(owner).expect("loop destination for break;");
                        ctxt.may_break = true;
                    }
                    return Ty::new_never(self.tcx);
                } else {
                    return Ty::new_error(self.tcx);
                }
            }
            ast::StmtKind::Err => (),
        }
        Ty::new_primitive(self.tcx, types::Primitive::Void)
    }

    fn check_expr_integer(&mut self, int: u64, sign: NumberSign, expected: Option<Ty<'tcx>>) -> Ty<'tcx> {
        if let Some(expected @ Ty(types::TyKind::Primitive(primitive))) = expected {
            if primitive.integer_fit(int, sign) {
                return expected;
            }
        }
        for primitive in [Primitive::Int, Primitive::Long, Primitive::ULong] {
            if primitive.integer_fit(int, sign) {
                return Ty::new_primitive(self.tcx, primitive);
            }
        }
        panic!("u64 to big for ulong ???")
    }

    fn check_block(&mut self, block: &'tcx ast::Block, expectation: Expectation<'tcx>) -> Ty<'tcx> {
        for stmt in &block.stmts {
            self.maybe_warn_unreachable(stmt.span, "statement");

            let prev_diverge = self.diverges.replace(Diverges::Maybe);
            if let Ty(types::TyKind::Never) = self.check_stmt(stmt) {
                self.diverges.set(std::cmp::max(self.diverges.get(), Diverges::Always(stmt.span)));
            }

            self.diverges.set(std::cmp::max(self.diverges.get(), prev_diverge));
        }

        let ty = if let Diverges::Maybe = self.diverges.get() {
            Ty::new_primitive(self.tcx, types::Primitive::Void)
        } else {
            Ty::new_never(self.tcx)
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
        use ast::Constant as Cnst;
        match kind {
            ast::ExprKind::BinOp(binop) =>
                self.check_expr_ty_definite(&binop.lhs.kind) && self.check_expr_ty_definite(&binop.rhs.kind),
            ast::ExprKind::Cast(_, ty, _) => ty.is_some(),
            ast::ExprKind::UnaryOp(expr, _) => self.check_expr_ty_definite(&expr.kind),
            ast::ExprKind::Range(lower, upper, _) =>
                self.check_expr_ty_definite(&lower.kind) && self.check_expr_ty_definite(&upper.kind),
            ast::ExprKind::Constant(Cnst::Null | Cnst::Integer(..)) => false,
            ast::ExprKind::Tuple(exprs) => {
                for expr in exprs {
                    if !self.check_expr_ty_definite(&expr.kind) {
                        return false;
                    }
                }
                true
            }
            ast::ExprKind::ShorthandEnum(..) => false,
            ast::ExprKind::Block(_) => true, // block is to complicated, so it's going to be matched
            ast::ExprKind::FunctionCall(..) | ast::ExprKind::TypeInit(..) |
            ast::ExprKind::Subscript(..) | ast::ExprKind::Field(..) |
            ast::ExprKind::String(..) | ast::ExprKind::Name(..) |
            ast::ExprKind::EnumVariant(..) | ast::ExprKind::Deref(..) |
            ast::ExprKind::Constant(..) | ast::ExprKind::Err => true,
        }
    }

    fn check_op_between(&self, op: lexer::BinaryOp, lhs: Ty<'tcx>, rhs: Ty<'tcx>) -> Option<Ty<'tcx>> {
        const OPERATOR_SIZES: [types::Primitive; 10] = {
            use types::Primitive::*;
            [SByte, Byte, Short, UShort, Int, Uint, Long, ULong, Nint, NUint]
        };

        macro_rules! boolop {
            ($ret:expr) => {{
                use lexer::BinaryOp::*;
                if let GreaterThan | GreaterEqual | LessThan | LessEqual = op {
                    return Some(Ty::new_primitive(self.tcx, types::Primitive::Bool));
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
        fn get_int(ty: Ty<'_>) -> Option<types::Primitive> {
            use types::Primitive::*;

            match ty { 
                Ty(types::TyKind::Primitive(p @
                        (SByte | Byte | Short | UShort | Int | Uint | Long | ULong | Nint | NUint))) =>
                    Some(*p),
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
            boolop!(Ty::new_primitive(self.tcx, lhs_int));
        }

        // TODO: cosider operator symmetry (Plus, Mul, BitwiseAnd, BitwiseOr, BitwiseXor)
        // TODO: for non symmetrical operators, if lhs.size() < rhs.size(), try to coerce lhs
        // upwards 

        // For now, we assume lhs.size() > rhs.size()
        let lhs_signed = lhs_int.signed().unwrap();
        for int in OPERATOR_SIZES.iter().rev() {
            if int.size() >= lhs_int.size() {
                continue;
            }
            let int_signed = unsafe { int.signed().unwrap_unchecked() };
            if !lhs_signed && int_signed {
                continue;
            }
            if *int == rhs_int {
                boolop!(Ty::new_primitive(self.tcx, lhs_int));
            }
        }

        return None;
    }

    fn check_expr_binop(&mut self, binop: &'tcx ast::BinOp, span: Span, expected: Option<Ty<'tcx>>) -> Ty<'tcx> {
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
                let lhs_ty = unsafe { *self.associations.get(&binop.lhs.node_id).unwrap_unchecked() };
                let rhs_ty = unsafe { *self.associations.get(&binop.rhs.node_id).unwrap_unchecked() };
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
                return Ty::new_primitive(self.tcx, types::Primitive::Bool);
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
                let lhs_ty = unsafe { *self.associations.get(&binop.lhs.node_id).unwrap_unchecked() };
                let rhs_ty = unsafe { *self.associations.get(&binop.rhs.node_id).unwrap_unchecked() };
                let Some(ret_ty) = self.check_op_between(binop.operator, lhs_ty, rhs_ty) else {
                    Message::error(
                        format!("operation {} is not defined between {lhs_ty} and {rhs_ty}", binop.operator))
                        .at(span)
                        .push(self.diagnostics());
                    return Ty::new_error(self.tcx);
                };
                {
                    use types::TyKind::{Primitive, Err, Never};
                    assert!(
                        matches!(ret_ty, Ty(Primitive(types::Primitive::Bool) | Err | Never)),
                        "some equality comparison does not produce boolean");
                }
                return Ty::new_primitive(self.tcx, types::Primitive::Bool);
            }
            BooleanAnd | BooleanOr => {
                self.check_expr_with_expectation(
                    &binop.lhs, Expectation::Coerce(Ty::new_primitive(self.tcx, types::Primitive::Bool)));

                self.check_expr_with_expectation(
                    &binop.rhs, Expectation::Coerce(Ty::new_primitive(self.tcx, types::Primitive::Bool)));

                return Ty::new_primitive(self.tcx, types::Primitive::Bool);
            }
        }
    }

    fn check_expr_unary(&mut self,
                      unop: lexer::UnaryOp, expr: &'tcx ast::Expr, expected: Option<Ty<'tcx>>) -> Ty<'tcx> {
        match unop {
            lexer::UnaryOp::Minus => {
                use types::TyKind::{Err, Never, Primitive};
                use types::Primitive::{SByte, Short, Int, Long, Nint};

                let expectation = match expected {
                    Some(expected) => Expectation::Guide(expected),
                    None => Expectation::None
                };
                let ty = self.check_expr_with_expectation(expr, expectation);
                let Ty(Primitive(SByte | Short | Int | Long | Nint) | Err | Never) = ty else {
                    Message::error(format!("negation `-` is not defined for type {ty}"))
                        .at(expr.span)
                        .push(self.diagnostics());
                    return Ty::new_error(self.tcx);
                };
                ty
            }
            lexer::UnaryOp::BitwiseNot => {
                use types::TyKind::{Err, Never, Primitive};
                use types::Primitive::{SByte, Byte, Short, UShort, Int, Uint, Long, ULong, Nint, NUint};

                let expectation = match expected {
                    Some(expected) => Expectation::Guide(expected),
                    None => Expectation::None
                };
                let ty = self.check_expr_with_expectation(expr, expectation);
                let Ty(Primitive(SByte | Byte | Short | UShort | Int | Uint | Long | ULong | Nint | NUint) | Err | Never) = ty else {
                    Message::error(format!("invert `~` is not defined for type {ty}"))
                        .at(expr.span)
                        .push(self.diagnostics());
                    return Ty::new_error(self.tcx);
                };
                ty
            }
            lexer::UnaryOp::Not => {
                let bool = Ty::new_primitive(self.tcx, types::Primitive::Bool);
                self.check_expr_with_expectation(expr, Expectation::Coerce(bool))
            }
            lexer::UnaryOp::Ref => {
                let expectation = match expected {
                    Some(Ty(types::TyKind::Refrence(ty))) => Expectation::Guide(*ty),
                    _ => Expectation::None
                };
                let ty = self.check_expr_with_expectation(expr, expectation);
                if let Ty(types::TyKind::Err | types::TyKind::Never) = ty {
                    return ty;
                }
                Ty::new_refrence(self.tcx, ty)
            }
        }
    }

    fn check_expr_call(&mut self, expr: &'tcx ast::Expr, args: &'tcx [ast::FunctionArgument], span: Span) -> Ty<'tcx> {
        let ty = self.check_expr_with_expectation(expr, Expectation::None);
        if let Ty(types::TyKind::Never | types::TyKind::Err) = ty {
            return ty;
        }
        let Ty(types::TyKind::Function(fn_def)) = ty else {
            Message::error(format!("expected function, found {ty}"))
                .at(expr.span)
                .push(self.diagnostics());
            return Ty::new_error(self.tcx);
        }; 

        let signature = self.tcx.fn_sig(*fn_def);

        let mut arg_count = 0;
        for (idx, arg) in args.iter().enumerate() {
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

    fn check_expr_subscript(&mut self, expr: &'tcx ast::Expr, args: &'tcx [ast::Expr]) -> Ty<'tcx> {
        let ty = self.check_expr_with_expectation(expr, Expectation::None);
        let index_span = unsafe {
            let start = args.first().unwrap_unchecked().span.start;
            let end = args.last().unwrap_unchecked().span.end;
            Span { start, end }
        };
        let base = {
            use types::TyKind::{Err, Never, Array, DynamicArray, Slice};
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
        if args.len() > 1 { 
            Message::error(
                format!("indexer of type {ty} expected 1 arugment, {} were supplied", args.len()))
                .at(index_span)
                .push(self.diagnostics());
        }
        let nuint = Ty::new_primitive(self.tcx, types::Primitive::NUint);
        let arg = self.check_expr_with_expectation(args.first().unwrap(), Expectation::Guide(nuint));
        if let Ty(types::TyKind::Err | types::TyKind::Never) = arg {
            return arg;
        }

        if let Ty(types::TyKind::Primitive(prim)) = arg {
            if !prim.signed().unwrap_or(true) {
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
        let Ty(types::TyKind::Tuple(tys)) = self.autoderef(ty, -1).unwrap_or(ty) else {
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

    fn check_expr_field(&mut self, expr: &'tcx ast::Expr, field: &'tcx ast::FieldIdent, node_id: ast::NodeId) -> Ty<'tcx> {
        let ty = self.check_expr_with_expectation(expr, Expectation::None); 
        if let Ty(types::TyKind::Never | types::TyKind::Err) = ty {
            return ty;
        }
        let field = match field {
            ast::FieldIdent::Named(ident) => ident,
            ast::FieldIdent::Tuple { value, span } =>
                return self.check_expr_ftuple(ty, *value as usize, *span),
        };
        let Ty(types::TyKind::Adt(adt_def)) = self.autoderef(ty, -1).unwrap_or(ty) else {
            Message::error(format!("fields are only found on structs {ty}"))
                .at(expr.span)
                .push(self.diagnostics());
            return Ty::new_error(self.tcx);
        };

        // types::AdtKind::Enum => {
        //     self.diagnostics.error(format!("can't find variant `{}` on enum {ty}", field.symbol.get()))
        //         .at(field.span);
        // }

        let Some((idx, fdef)) = adt_def.fields()
            .find(|(_, fdef)| fdef.symbol == field.symbol) else {
            match adt_def.kind {
                types::AdtKind::Enum =>
                    unreachable!("Enum shouldn't apear here"),
                types::AdtKind::Struct => {
                    Message::error(format!("can't find field `{}` on struct {ty}", field.symbol.get()))
                        .at(field.span)
                        .push(self.diagnostics());
                }
                types::AdtKind::Union =>
                    panic!("unions are not even parsable with this parser")
            }
            return Ty::new_error(self.tcx);
        };

        self.field_indices.insert(node_id, idx);
        self.tcx.type_of(fdef.def)
    }
 
    fn check_expr_variant(
        &mut self, ty_expr: Option<&'tcx ast::TypeExpr>,
        variant: &'tcx ast::Ident, node_id: ast::NodeId, expected: Option<Ty<'tcx>>, span: Span) -> Ty<'tcx> {
        let ty = ty_expr.map(|expr| self.lowering_ctxt.lower_ty(expr));
        
        let Some(ty) = ty.or(expected) else {
            Message::error(format!("can't infer enum of shortand variant"))
                .at(span)
                .push(self.diagnostics());
            return Ty::new_error(self.tcx);
        };

        if let Ty(types::TyKind::Never | types::TyKind::Err) = ty {
            return ty;
        }

        let Ty(types::TyKind::Adt(adt_def)) = ty else {
            Message::error(format!("variants are only found on enums {ty}"))
                .at(span)
                .push(self.diagnostics());
            return Ty::new_error(self.tcx);
        };


        match adt_def.kind {
            types::AdtKind::Enum => (),
            types::AdtKind::Union =>
                panic!("unions are not even parsable with this parser"),
            types::AdtKind::Struct =>
                unreachable!("its an ENUM variant")
        }

        let Some((idx, _)) = adt_def.fields()
            .find(|(_, vriant)| vriant.symbol == variant.symbol) else {
            Message::error(format!("can't find variant `{}` on enum {ty}", variant.symbol.get()))
                .at(variant.span)
                .push(self.diagnostics());
            return Ty::new_error(self.tcx);
        };

        self.variant_translations.insert(node_id, idx);
        ty
    }

    fn check_expr_init(
        &mut self, ty_epxr: Option<&'tcx TypeExpr>,
        inits: &'tcx [ast::TypeInit], expected: Option<Ty<'tcx>>, span: Span) -> Ty<'tcx> {
        let ty = ty_epxr.map(|expr| self.lowering_ctxt.lower_ty(expr));
        
        let Some(ty) = ty.or(expected) else {
            Message::error("can't infer type of anonymous init expresssion")
                .at(span)
                .push(self.diagnostics());
            return Ty::new_error(self.tcx);
        };

        use types::TyKind;
        match ty {
            Ty(TyKind::Primitive(..)) => {
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
                for init in inits {
                    match init {
                        ast::TypeInit::Direct(expr) => {
                            self.check_expr_with_expectation(expr, Expectation::Coerce(*base));
                        }
                        ast::TypeInit::Field(ident, expr) => {
                            Message::error("field initializer in array initialization is invalid")
                                .at(Span::new(ident.span.start, expr.span.end))
                                .push(self.diagnostics());
                        }
                    }
                }
                
                let count = inits.len();
                match kind {
                    types::TyKind::Array(_, capcity) => {
                        let capacity = capcity.try_as_usize()
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
            Ty(TyKind::Adt(atd_def)) => match atd_def.kind {
                types::AdtKind::Struct => {
                    let fields: HashMap<_, _, ahash::RandomState> = atd_def.fields()
                        .map(|(idx, fdef)| (fdef.symbol, (idx, fdef)))
                        .collect();
                    for init in inits {
                        match init {
                            ast::TypeInit::Field(ident, expr) => {
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
                            ast::TypeInit::Direct(expr) if matches!(expr.kind, ast::ExprKind::Name(..)) => {
                                let ident = match &expr.kind {
                                    ast::ExprKind::Name(ast::QName::Unresolved(ident)) => ident,
                                    ast::ExprKind::Name(ast::QName::Resolved { ident, .. }) => ident,
                                    _ => unreachable!()
                                };
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
                            ast::TypeInit::Direct(expr) => {
                                Message::error("immediate initializer in struct initialization is invalid")
                                    .at(expr.span)
                                    .push(self.diagnostics());
                            }
                        }
                    }
                }
                types::AdtKind::Enum => {
                    Message::error(format!("expected struct, found enum {ty}"))
                        .at(span)
                        .note(format!("initialize an enum with {}.<variant> syntax", atd_def.name.get()))
                        .push(self.diagnostics());
                }
                types::AdtKind::Union =>
                    panic!("unions are not even parsable with this parser"),
            }
            Ty(TyKind::Function(..)) => unreachable!(),
            Ty(TyKind::Range(..)) => unreachable!(),
            Ty(TyKind::Never | TyKind::Err) => ()
        }

        ty
    }

    fn check_valid_cast(&self, from: Ty<'tcx>, to: Ty<'tcx>) -> bool {
        use types::TyKind::{Err, Never, Primitive};
        if let Ty(Err | Never) = from {
            return true;
        }
        if let Ty(Err | Never) = to {
            return true;
        }

        let Ty(Primitive(from)) = from else {
            return false;
        };

        let Ty(Primitive(to)) = to else {
            return false;
        };

        if from.signed().is_some() && to.signed().is_some() {
            // both are numbers
            // which are always castable between each other
            return true;
        }

        // u32 <-> char conversions are also valid
        return match (from, to) {
            (types::Primitive::Uint, types::Primitive::Char) => true,
            (types::Primitive::Char, types::Primitive::Uint) => true,
            _ => false
        };
    }

    fn check_expr_conv(
        &mut self, expr: &'tcx ast::Expr, ty_expr: Option<&'tcx ast::TypeExpr>, conversion: ast::TypeConversion, expected: Option<Ty<'tcx>>, span: Span) -> Ty<'tcx> {

        let ty = ty_expr.map(|expr| self.lowering_ctxt.lower_ty(expr));
        
        let Some(ty) = ty.or(expected) else {
            let tc = match conversion {
                ast::TypeConversion::Cast => "cast",
                ast::TypeConversion::Transmute => "transmute",
            };
            Message::error(format!("can't infer type of auto {}", tc))
                .at(span)
                .push(self.diagnostics());
            return Ty::new_error(self.tcx);
        };

        let expr_ty = self.check_expr_with_expectation(expr, Expectation::None);

        match conversion {
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

    fn check_expr_tuple(&mut self, exprs: &'tcx [ast::Expr], expected: Option<Ty<'tcx>>) -> Ty<'tcx> {
        let expected_list = match expected {
            Some(Ty(types::TyKind::Tuple(tys))) => Some(tys),
            _ => None,
        };
        let mut tys = Vec::new();
        if let Some(expected_list) = expected_list {
            for (expr, exp) in exprs.iter().zip(expected_list) {
                let ty = self.check_expr_with_expectation(expr, Expectation::Guide(*exp));
                tys.push(ty);
            }
        } else {
            for expr in exprs {
                let ty = self.check_expr_with_expectation(expr, Expectation::None);
                tys.push(ty);
            }
        }
        Ty::new_tuple(self.tcx, tys)
    }

    fn check_expr(&mut self, expr: &'tcx ast::Expr, expected: Option<Ty<'tcx>>) -> Ty<'tcx> {
        use NumberSign::*;
        match &expr.kind {
            ast::ExprKind::String(..) => 
                Ty::new_primitive(self.tcx, Primitive::String),
            ast::ExprKind::Constant(ast::Constant::Boolean(..)) =>
                Ty::new_primitive(self.tcx, Primitive::Bool),
            ast::ExprKind::Constant(ast::Constant::Char(..)) =>
                Ty::new_primitive(self.tcx, Primitive::Char),
            ast::ExprKind::Constant(ast::Constant::Integer(int)) =>
                self.check_expr_integer(*int, Positive, expected),
            ast::ExprKind::Constant(ast::Constant::Floating(..)) => todo!(),
            ast::ExprKind::Constant(ast::Constant::Null) => {
                let Some(expected) = expected else {
                    Message::error("can't infer type of anonymous null")
                        .at(expr.span)
                        .push(self.diagnostics());
                    return Ty::new_error(self.tcx);
                };
                let Ty(types::TyKind::Never | types::TyKind::Err | types::TyKind::Refrence(..)) = expected else {
                    Message::error(format!("non refrence-type {expected} cannot be null"))
                        .at(expr.span)
                        .push(self.diagnostics());
                    return expected
                };
                expected
            }
            ast::ExprKind::UnaryOp(expr, lexer::UnaryOp::Minus)
                if matches!(expr.kind, ast::ExprKind::Constant(ast::Constant::Integer(..))) => {
                let ast::ExprKind::Constant(ast::Constant::Integer(int)) = expr.kind else {
                    unreachable!()
                };
                self.check_expr_integer(int, Negative, expected)
            }
            ast::ExprKind::BinOp(binop) =>
                self.check_expr_binop(binop, expr.span, expected),
            ast::ExprKind::UnaryOp(expr, unop) => 
                self.check_expr_unary(*unop, expr, expected),
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
            ast::ExprKind::Block(block) =>
                self.check_block(block, Expectation::None), 
            ast::ExprKind::Err =>
                Ty::new_error(self.tcx),
            ast::ExprKind::FunctionCall(base, args, _) =>
                self.check_expr_call(base, args, expr.span),
            ast::ExprKind::Subscript(base, args) =>
                self.check_expr_subscript(base, args),
            ast::ExprKind::Field(base, field) =>
                self.check_expr_field(base, field, expr.node_id),
            ast::ExprKind::TypeInit(ty_expr, init) =>
                self.check_expr_init(ty_expr.as_deref(), init, expected, expr.span),
            ast::ExprKind::Cast(conv, ty, kind) =>
                self.check_expr_conv(conv, ty.as_deref(), *kind, expected, expr.span),
            ast::ExprKind::Range(start, end, inclusive) => {
                {
                    let mut start = &start;
                    let mut end = &end;
                    if !self.check_expr_ty_definite(&start.kind) && self.check_expr_ty_definite(&end.kind) {
                        (start, end) = (end, start);
                    }

                    let nuint = Ty::new_primitive(self.tcx, types::Primitive::NUint);
                    let expectation = Expectation::Guide(nuint);
                    let start_ty = self.check_expr_with_expectation(start, expectation);
                    self.check_expr_with_expectation(end, Expectation::Guide(start_ty));
                }
                use types::{
                    TyKind::{Never, Err, Primitive},
                    Primitive::{SByte, Byte, Short, UShort, Int, Uint, Long, ULong, Nint, NUint, Char}
                };

                let start_ty = unsafe { *self.associations.get(&start.node_id).unwrap_unchecked() };
                let end_ty = unsafe { *self.associations.get(&end.node_id).unwrap_unchecked() };
                let mut has_error = false;
                if start_ty != end_ty {
                    self.maybe_emit_type_error(end_ty, start_ty, expr.span);
                    has_error = true;
                }
                if !matches!(
                    start_ty, 
                    Ty(Never | Err | 
                       Primitive(SByte | Byte | Short | UShort | Int | Uint | Long | ULong | Nint | NUint | Char))) {
                    Message::error(
                        format!("type {start_ty} is not steppable")
                    )
                        .at(start.span)
                        .push(self.diagnostics());
                    has_error = true;
                }
                if !matches!(
                    end_ty, 
                    Ty(Never | Err | 
                       Primitive(SByte | Byte | Short | UShort | Int | Uint | Long | ULong | Nint | NUint | Char))) {
                    Message::error(
                        format!("type {end_ty} is not steppable")
                    )
                        .at(end.span)
                        .push(self.diagnostics());
                    has_error = true;
                }
                if has_error {
                    return Ty::new_error(self.tcx);
                }
                Ty::new_range(self.tcx, start_ty, *inclusive)
            }
            ast::ExprKind::Tuple(exprs) =>
                self.check_expr_tuple(exprs, expected),
            ast::ExprKind::EnumVariant(ty, variant) =>
                self.check_expr_variant(Some(ty), variant, expr.node_id, expected, expr.span),
            ast::ExprKind::ShorthandEnum(variant) =>
                self.check_expr_variant(None, variant, expr.node_id, expected, expr.span),
        }
    }

    fn check_expr_name(&mut self, name: &ast::QName) -> Ty<'tcx> {
        let ast::QName::Resolved { res_kind, .. } = name else {
            panic!("unresolved Name in check_expr_name(...)");
        };
        match res_kind {
            ast::Resolution::Local(node_id) => 
                *self.associations.get(node_id)
                    .expect("check_expr_name(...) unknown Local(NodeId)"),
            ast::Resolution::Def(def_id, DefinitionKind::Function | DefinitionKind::Const | DefinitionKind::Global) =>
                self.tcx.type_of(*def_id),
            ast::Resolution::Err => Ty::new_error(self.tcx),
            ast::Resolution::Primitive |
            ast::Resolution::Def(_, DefinitionKind::Enum | DefinitionKind::Struct) => 
                panic!("type-like resolution in check_expr_name"),
        }
    }

    fn check_expr_with_expectation(&mut self, expr: &'tcx ast::Expr, expectation: Expectation<'tcx>) -> Ty<'tcx> {
        let expected = match expectation {
            Expectation::None => None,
            Expectation::Guide(ty) | Expectation::Coerce(ty) => Some(ty)
        };

        let prev_diverge = self.diverges.get();
        self.diverges.set(Diverges::Maybe);
        let ty = self.check_expr(&expr, expected); 

        if let Expectation::Coerce(expected) = expectation {
            self.maybe_emit_type_error(ty, expected, expr.span);
        }

        self.maybe_warn_unreachable(expr.span, "expression");

        if let Ty(types::TyKind::Never) = ty {
            self.diverges.set(std::cmp::max(self.diverges.get(), Diverges::Always(expr.span)));
        }

        self.ty_assoc(expr.node_id, ty);

        self.diverges.set(std::cmp::max(self.diverges.get(), prev_diverge));

        ty
    }

    fn check_return_ty(&mut self, expr: &'tcx ast::Expr, ret_ty: Ty<'tcx>, ret_ty_span: Span) {
        self.return_ty = Some(ret_ty);

        let ty = self.check_expr(&expr, Some(ret_ty));
        self.maybe_emit_type_error(ty, ret_ty, ret_ty_span);

        if matches!(ret_ty, Ty(types::TyKind::Primitive(types::Primitive::Void))) &&
            matches!(ty, Ty(types::TyKind::Never)) {
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
        found
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

    fn lower_name(&self, name: &ast::QName) -> Ty<'tcx> {
        let ast::QName::Resolved { res_kind, ident } = name else {
            panic!("unresolved Name in lower_name(...)");
        };
        match res_kind {
            ast::Resolution::Primitive => {
                let primitive = Primitive::try_from(ident.symbol)
                    .expect("non-primitive Ident for primitive name resolution");
                Ty::new_primitive(self.tcx, primitive)
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
            ast::TypeExprKind::Array(ty, cap) => {
                match &cap {
                    ast::ArrayCapacity::Discrete(..) | ast::ArrayCapacity::Infer => {
                        let ty = self.lower_ty(ty);
                        if let Ty(types::TyKind::Err) = ty {
                            return ty;
                        }

                        let cap = if let ast::ArrayCapacity::Discrete(expr) = cap {
                            types::Const::from_definition(self.tcx, expr.def_id)
                        } else {
                            self.tcx.intern(ConstInner::Placeholder)
                        };

                        if let types::Const(types::ConstInner::Err { msg, span }) = &cap {
                            Message::error(msg)
                                .at(*span)
                                .push(self.diagnostics());
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
                if let Ty(types::TyKind::Err) = ty {
                    return ty;
                }
                Ty::new_slice(self.tcx, ty)
            }
            ast::TypeExprKind::Tuple(exprs) => {
                let mut tys = Vec::new();
                for expr in exprs {
                    let ty = self.lower_ty(expr);
                    if let Ty(types::TyKind::Err) = ty {
                        return ty;
                    }
                    tys.push(ty);
                }
                Ty::new_tuple(self.tcx, tys)
            }
            ast::TypeExprKind::Generic(..) => panic!("lowering generic types is not supported yet")
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
                let fields = enm.variants.iter().map(|variant| {
                    assert_ne!(variant.def_id, ast::DEF_ID_UNDEF,
                               "variant {:?} of enum {:?} is undefined", variant.name.symbol, item.ident.symbol);
                    types::FieldDef { def: variant.def_id, symbol: variant.name.symbol }
                }).collect();
                let adt_def = tcx.intern(
                    types::AdtDefInner::new(def_id, item.ident.symbol, fields, types::AdtKind::Enum));
                Ty::new_adt(tcx, adt_def)
            }
            ast::ItemKind::Struct(stc) => {
                let fields = stc.fields.iter().map(|fdef| {
                    assert_ne!(fdef.def_id, ast::DEF_ID_UNDEF,
                               "field {:?} of struct {:?} is undefined", fdef.name.symbol, item.ident.symbol);
                    types::FieldDef { def: fdef.def_id, symbol: fdef.name.symbol }
                }).collect();
                let adt_def = tcx.intern(
                    types::AdtDefInner::new(def_id, item.ident.symbol, fields, types::AdtKind::Struct));
                Ty::new_adt(tcx, adt_def)
            },
            ast::ItemKind::GlobalVar(expr, ..) => {
                let ctxt = LoweringCtxt::new(tcx);
                ctxt.lower_ty(&expr)
            },
            ast::ItemKind::Err =>
                panic!("resolved Err to Definiton")
        }
        ast::Node::Field(field) => {
            let ctx = LoweringCtxt::new(tcx);
            ctx.lower_ty(&field.ty)
        }
        ast::Node::NestedConst(_nested) => {
            // FIXME: GenericArgs aren't supported at all currently,
            // making the only other place for a NestedConst ArrayCap,
            // which is always nuint
            Ty::new_primitive(tcx, types::Primitive::NUint)
        }
        _ => panic!("only items can be declarations")
    }
}

pub struct TypecheckResults;

pub fn typecheck(tcx: TyCtxt<'_>, def_id: DefId) -> &'_ TypecheckResults {
    let node = tcx.node_by_def_id(def_id);

    let body = node.body()
        .expect("typecheck on node without a body");

    let mut ctxt = TypecheckCtxt::new(tcx);

    if let Some(ast::FnSignature { returns, .. }) = node.signature() {
        let sig = tcx.fn_sig(def_id);
        for param in sig.params {
            ctxt.ty_assoc(param.node_id, param.ty);
        }
        ctxt.check_return_ty(body.body, sig.returns, returns.span);
    } else {
        let ty = tcx.type_of(def_id);
        ctxt.check_expr_with_expectation(body.body, Expectation::Coerce(ty));
    }

    &TypecheckResults
}

pub fn fn_sig(tcx: TyCtxt<'_>, def_id: DefId) -> types::Signature {
    let node = tcx.node_by_def_id(def_id);
    let ctxt = LoweringCtxt::new(tcx);

    match node {
        ast::Node::Item(ast::Item { kind: ast::ItemKind::Function(func), ident, .. }) => {
            let mut returns = ctxt.lower_ty(&func.sig.returns);
            if returns.is_incomplete() {
                Message::error(
                    format!("type {returns} is incomplete, incomplete types are not allowed in function signatures"))
                    .at(func.sig.returns.span)
                    .push(tcx.diagnostics());
                returns = Ty::new_error(tcx);
            }

            let mut params = Vec::new();
            for param in &func.sig.params {
                let mut ty = ctxt.lower_ty(&param.ty);
                let name = param.ident.symbol;

                if ty.is_incomplete() {
                    Message::error(format!("type {ty} is incomplete, incomplete types are not allowed in function signatures"))
                        .at(param.ty.span)
                        .push(tcx.diagnostics());
                    ty = Ty::new_error(tcx);
                }


                params.push(types::Param {
                    name,
                    ty,
                    node_id: param.node_id
                });
            }
            let params: Box<[types::Param]> = params.into_boxed_slice();
            let params: &'_ [types::Param] = tcx.arena.alloc(params);

            types::Signature { returns, params, name: ident.symbol }
        }
        _ => {
            panic!("non-function definition in fn_sig")
        }
    }
}
