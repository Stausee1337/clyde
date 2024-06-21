use core::panic;
use std::{collections::HashMap, ops::Range};

use crate::{context::TyCtxt, types::{Ty, Const, ConstInner, Primitive, TyKind, NumberSign, self}, ast::{DefId, self, DefinitionKind, ControlFlow}, interface, diagnostics::Diagnostics, symbol};

struct Rib<'tcx> {
    kind: RibKind,
    owner: ast::NodeId,
    expected_ty: Option<Ty<'tcx>>
}

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

#[derive(PartialEq, Eq)]
enum RibKind {
    If, Loop, Block,
}

#[derive(Default)]
struct DivergingTy<'tcx> {
    result_ty: Option<Ty<'tcx>>,
    // ONLY true if a statement diverges COMPLETELY,
    // and does no longer continue on the applications
    // main path in ANY way!
    // eg. if ... { return ...; } would have this property `true`
    diverges: bool
}

impl<'tcx> DivergingTy<'tcx> {
    fn never_diverges(tcx: TyCtxt<'tcx>, diverges: bool) -> Self {
        Self {
            result_ty: Some(Ty::new_never(tcx)),
            diverges
        }
    }
}

struct TypecheckCtxt<'tcx> {
    tcx: TyCtxt<'tcx>,
    ribs: Vec<Rib<'tcx>>,
    outer_rib: Option<Rib<'tcx>>,
    diagnostics: Diagnostics<'tcx>,
    lowering_ctxt: LoweringCtxt<'tcx>,
    associations: HashMap<ast::NodeId, Ty<'tcx>, ahash::RandomState>,
}

impl<'tcx> TypecheckCtxt<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            ribs: Vec::new(),
            outer_rib: None,
            lowering_ctxt: LoweringCtxt::new(tcx),
            diagnostics: tcx.diagnostics_for_file(interface::INPUT_FILE_IDX),
            associations: Default::default()
        }
    }

    fn with_rib<T, F: FnOnce(&mut Self) -> T>(
        &mut self,
        kind: RibKind,
        owner: ast::NodeId,
        expected_ty: Option<Ty<'tcx>>,
        do_work: F
    ) -> T {
        let is_outer_rib = self.outer_rib
            .as_ref()
            .map(|rib| rib.owner == owner)
            .unwrap_or(false);
        if !is_outer_rib {
            self.ribs.push(Rib { kind, owner, expected_ty });
        } else {
            let rib_ty = self.outer_rib.as_ref().unwrap().expected_ty;
            assert_eq!(expected_ty, rib_ty, "Expected type of owning root block is unequal to expected type of outer_rib");
        }
        let rv = do_work(self);
        if !is_outer_rib {
            self.ribs.pop();
        }
        rv
    }

    fn find_rib(&mut self, kind: RibKind) -> Option<&Rib<'tcx>> {
        let mut result = None;
        for rib in self.ribs.iter() {
            if rib.kind == kind {
                result = Some(rib);
                break;
            }
        }

        result
    }

    fn ty_assoc(&mut self, node_id: ast::NodeId, ty: Ty<'tcx>) {
        if let Some(prev) = self.associations.insert(node_id, ty) {
            assert_eq!(ty, prev, "tried to assoicate {node_id:?} twice with different types; First {prev:?} then {ty:?}");
            println!("[WARNING] unwanted attempt to associate {node_id:?} with {ty:?} twice")
        }
    }

    fn check_stmt_assign(&mut self, lhs: &'tcx ast::Expr, rhs: &'tcx ast::Expr) -> bool {
        let is_valid_lhs = {
            use ast::ExprKind::{Subscript, Attribute, Name, Deref};
            matches!(lhs.kind, Subscript(..) | Attribute(..) | Name(..) | Deref(..)) 
        };
        if !is_valid_lhs {
            self.diagnostics.error("invalid left hand side in assignment")
                .with_span(lhs.span.clone());
        }
        let lhs_ty = self.check_expr_with_expectation(lhs, Expectation::None);
        if let Ty(types::TyKind::Never) = self.check_expr_with_expectation(rhs, Expectation::Coerce(lhs_ty)) {
            return true;
        }
        false
    }

    fn check_stmt_if(
        &mut self,
        condition: &'tcx ast::Expr, body: &'tcx [ast::Stmt], else_branch: Option<&'tcx ast::Stmt>, owner: ast::NodeId) -> DivergingTy<'tcx> {
        self.check_expr_with_expectation(
            condition, Expectation::Coerce(Ty::new_primitive(self.tcx, types::Primitive::Bool)));

        let mut body_ty = self.with_rib(RibKind::If, owner, None, |this| this.visit_block(body));

        if let Some(else_branch) = else_branch {
            let else_ty = match &else_branch.kind {
                ast::StmtKind::If(condition, body, branch) =>
                    self.check_stmt_if(condition, body, branch.as_deref(), else_branch.node_id),
                ast::StmtKind::Expr(expr) if matches!(expr.kind, ast::ExprKind::Block(..)) => {
                    let else_body = match &expr.kind {
                        ast::ExprKind::Block(block) => block,
                        _ => unreachable!()
                    };
                    
                    self.visit_block(else_body)
                }
                _ => unreachable!()
            };

            let result_ty = match Option::zip(body_ty.result_ty, else_ty.result_ty) {
                Some((body_ty, else_ty)) => {
                    self.maybe_emit_type_error(else_ty, body_ty, else_branch.span.clone());
                    Some(body_ty)
                }
                None => None,
            };

            body_ty = DivergingTy {
                result_ty,
                diverges: body_ty.diverges && else_ty.diverges
            };
        } else {
            body_ty.diverges = false;
        }

        body_ty
    }

    fn check_stmt_local(&mut self,
        stmt: &'tcx ast::Stmt, expr: Option<&'tcx ast::Expr>, ty: Option<&'tcx ast::TypeExpr>) -> bool {
        let expected = ty.map(|ty| self.lowering_ctxt.lower_ty(&ty));
        if expected.is_none() && expr.is_none() {
            self.diagnostics.error("type-anonymous variable declarations require an init expresssion")
                .with_span(stmt.span.clone());
            self.ty_assoc(stmt.node_id, Ty::new_error(self.tcx));
            return false;
        } else if let Some(expr) = expr {
            let ty = self.check_expr_with_expectation(expr, expected.into());
            if let Ty(types::TyKind::Never) = ty {
                self.ty_assoc(stmt.node_id, expected.unwrap_or(ty)); 
                // TODO: figure out what really to do with that
                // maybe some sort of a `Bendable` TyKind, for this
                // specific situations. For now its `Never`
                // eg. var test = todo();                                                        
                return true;
            }
            self.ty_assoc(stmt.node_id, ty);
        } else if let Some(expected) = expected {
            // TODO: check if TyKind can acutally be instantiated like this:
            // Type var; So to speak, checking if a type is fully defaultable
            self.ty_assoc(stmt.node_id, expected);
        } else {
            unreachable!()
        }
        false
    }

    fn check_stmt(&mut self, stmt: &'tcx ast::Stmt) -> DivergingTy<'tcx> {
        match &stmt.kind {
            ast::StmtKind::Expr(expr) => {
                let ty = self.check_expr_with_expectation(expr, Expectation::None);
                if let Ty(types::TyKind::Never) = ty {
                    return DivergingTy::never_diverges(self.tcx, true);
                }
            }
            ast::StmtKind::Assign(lhs, rhs) =>
                return DivergingTy::never_diverges(self.tcx, self.check_stmt_assign(lhs, rhs)),
            ast::StmtKind::If(condition, body, branch) =>
                return self.check_stmt_if(condition, body, branch.as_deref(), stmt.node_id),
            ast::StmtKind::Local(_, ty, expr) =>
                return DivergingTy::never_diverges(
                    self.tcx, self.check_stmt_local(stmt, expr.as_deref(), ty.as_deref())),
            ast::StmtKind::Return(expr) => {
                let Some(Some(return_ty)) = self.outer_rib.as_ref().map(|rib| rib.expected_ty) else {
                    self.diagnostics.error("`return` found outside of function body")
                        .with_span(stmt.span.clone());
                    self.diagnostics.note("use break ...; for producing values")
                        .with_span(stmt.span.clone());
                    return DivergingTy::default();
                };
                let ty = expr
                    .as_ref()
                    .map(|expr| self.check_expr_with_expectation(expr, Expectation::Coerce(return_ty)));
                let ty = match ty {
                    Some(ty) => ty,
                    None => {
                        let ty = Ty::new_primitive(self.tcx, types::Primitive::Void);
                        self.maybe_emit_type_error(ty, return_ty, stmt.span.clone());
                        ty
                    }
                };
                self.ty_assoc(stmt.node_id, ty);
                return DivergingTy {
                    diverges: true,
                    result_ty: Some(Ty::new_never(self.tcx))
                };
            }
            ast::StmtKind::ControlFlow(flow) => {
                let Some(lop) = self.find_rib(RibKind::Loop) else {
                    self.diagnostics.error(format!("`{}` found outside of loop", flow.kind))
                        .with_span(stmt.span.clone());
                    return DivergingTy::default();
                };
                flow.res.set(lop.owner).unwrap();
                return DivergingTy {
                    result_ty: None,
                    diverges: true
                };
            }
            ast::StmtKind::Err => (),
            _ => todo!("Unimplemented Stmt Kind")
        }
        DivergingTy::default()
    }

    fn check_expr_integer(&mut self, int: u64, sign: NumberSign, expected: Option<Ty<'tcx>>) -> Ty<'tcx> {
        if let Some(Ty(TyKind::Primitive(primitive))) = expected {
            if primitive.integer_fit(int, sign) {
                return expected.unwrap();
            }
        }
        for primitive in [Primitive::Int, Primitive::Long, Primitive::ULong] {
            if primitive.integer_fit(int, sign) {
                return Ty::new_primitive(self.tcx, primitive);
            }
        }
        panic!("u64 to big for ulong ???")
    }

    fn visit_block(&mut self, stmts: &'tcx [ast::Stmt]) -> DivergingTy<'tcx> {
        let mut iterator = stmts.iter();
        let mut result_ty = None;
        let mut diverges = false;
        for stmt in &mut iterator {
            let result = self.check_stmt(stmt);
            if result.diverges {
                diverges = true;
                result_ty = result.result_ty;
                break;
            }
        }

        if result_ty.is_some() {
            if let Some(stmt) = iterator.next() {
                self.diagnostics.warning("this code is unreachable")
                    .with_span(stmt.span.clone());
            }
        }

        return DivergingTy {
            diverges,
            result_ty
        };
    }

    fn check_expr_block(&mut self, stmts: &'tcx [ast::Stmt], owner: ast::NodeId, expected: Option<Ty<'tcx>>) -> Ty<'tcx> {
        self.with_rib(RibKind::Block, owner, expected, |this| {
            let result_ty = this.visit_block(stmts).result_ty;
            result_ty.unwrap_or_else(|| Ty::new_primitive(this.tcx, types::Primitive::Void))
        })
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
            ast::ExprKind::Block(_) => true, // block is to complicated, so it's going to be matched
            ast::ExprKind::FunctionCall(..) | ast::ExprKind::TypeInit(..) |
            ast::ExprKind::Subscript(..) | ast::ExprKind::Attribute(..) |
            ast::ExprKind::String(..) | ast::ExprKind::Name(..) |
            ast::ExprKind::ShorthandEnum(..) | ast::ExprKind::Deref(..) |
            ast::ExprKind::Constant(..) | ast::ExprKind::Err => true
        }
    }

    fn check_op_between(&self, op: ast::BinaryOperator, lhs: Ty<'tcx>, rhs: Ty<'tcx>) -> Option<Ty<'tcx>> {
        const OPERATOR_SIZES: [types::Primitive; 10] = {
            use types::Primitive::*;
            [SByte, Byte, Short, UShort, Int, Uint, Long, ULong, Nint, NUint]
        };

        macro_rules! boolop {
            ($ret:expr) => {{
                use ast::BinaryOperator::*;
                if let GreaterThan | GreaterEqual | LessThan | LessEqual = op {
                    return Some(Ty::new_primitive(self.tcx, types::Primitive::Bool));
                }
                return Some($ret);
            }};
        }

        {
            use ast::BinaryOperator::*;
            let (Plus | Minus | Mul | Div | Mod |
                 ShiftLeft | ShiftRight | BitwiseAnd | BitwiseOr | BitwiseXor |
                 GreaterThan | GreaterEqual | LessThan | LessEqual) = op else {
                panic!("check_op_between used on invalid operator {op}");
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

    fn check_expr_binop(&mut self, binop: &'tcx ast::BinOp, span: Range<usize>, expected: Option<Ty<'tcx>>) -> Ty<'tcx> {
        use ast::BinaryOperator::*;
        match binop.operator {
            Plus | Minus | Mul | Div | Mod |
            ShiftLeft | ShiftRight | BitwiseAnd | BitwiseOr | BitwiseXor => {
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
                    self.diagnostics.error(
                        format!("operation {} is not defined between {lhs_ty} and {rhs_ty}", binop.operator))
                        .with_span(span);
                    return Ty::new_error(self.tcx);
                };
                return ret_ty;
            }
            Equal | NotEqual => {
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
                    self.diagnostics.error(
                        format!("operation {} is not defined between {lhs_ty} and {rhs_ty}", binop.operator))
                        .with_span(span);
                    return Ty::new_error(self.tcx);
                };
                assert!(
                    matches!(ret_ty, Ty(types::TyKind::Primitive(types::Primitive::Bool))),
                    "some equality comparison does not produce boolean");
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
                      unop: ast::UnaryOperator, expr: &'tcx ast::Expr, expected: Option<Ty<'tcx>>) -> Ty<'tcx> {
        match unop {
            ast::UnaryOperator::Neg => {
                use types::Primitive::{SByte, Short, Int, Long, Nint};
                let expectation = match expected {
                    Some(expected) => Expectation::Guide(expected),
                    None => Expectation::None
                };
                let ty = self.check_expr_with_expectation(expr, expectation);
                let Ty(types::TyKind::Primitive(SByte | Short | Int | Long | Nint)) = ty else {
                    self.diagnostics.error(format!("negation `-` is not defined for type {ty}"))
                        .with_span(expr.span.clone());
                    return Ty::new_error(self.tcx);
                };
                ty
            }
            ast::UnaryOperator::BitwiseInvert => {
                use types::Primitive::{SByte, Byte, Short, UShort, Int, Uint, Long, ULong, Nint, NUint};
                let expectation = match expected {
                    Some(expected) => Expectation::Guide(expected),
                    None => Expectation::None
                };
                let ty = self.check_expr_with_expectation(expr, expectation);
                let Ty(types::TyKind::Primitive(SByte | Byte | Short | UShort | Int | Uint | Long | ULong | Nint | NUint)) = ty else {
                    self.diagnostics.error(format!("invert `~` is not defined for type {ty}"))
                        .with_span(expr.span.clone());
                    return Ty::new_error(self.tcx);
                };
                ty
            }
            ast::UnaryOperator::BooleanNot => {
                let bool = Ty::new_primitive(self.tcx, types::Primitive::Bool);
                self.check_expr_with_expectation(expr, Expectation::Coerce(bool))
            }
            ast::UnaryOperator::Ref => {
                let expectation = match expected {
                    Some(Ty(types::TyKind::Refrence(ty))) => Expectation::Guide(*ty),
                    _ => Expectation::None
                };
                let ty = self.check_expr_with_expectation(expr, expectation);
                Ty::new_refrence(self.tcx, ty)
            }
        }
    }

    fn check_expr_call(&mut self, expr: &'tcx ast::Expr, args: &'tcx [ast::FunctionArgument], span: Range<usize>) -> Ty<'tcx> {
        let ty = self.check_expr_with_expectation(expr, Expectation::None);
        let Ty(types::TyKind::Function(fn_def)) = ty else {
            self.diagnostics.error(format!("exected function, found {ty}"))
                .with_span(expr.span.clone());
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
            self.diagnostics.error(
                format!("function {} expected {} arugments, {} were supplied",
                        signature.name.get(), signature.params.len(), arg_count))
                .with_span(span);
        }

        signature.returns
    }

    fn check_expr(&mut self, expr: &'tcx ast::Expr, expected: Option<Ty<'tcx>>) -> Ty<'tcx> {
        use NumberSign::*;
        match &expr.kind {
            ast::ExprKind::String(..) => 
                Ty::new_refrence(self.tcx, Ty::new_primitive(self.tcx, Primitive::String)),
            ast::ExprKind::Constant(ast::Constant::Boolean(..)) =>
                Ty::new_primitive(self.tcx, Primitive::Bool),
            ast::ExprKind::Constant(ast::Constant::Integer(int)) =>
                self.check_expr_integer(*int, Positive, expected),
            ast::ExprKind::Constant(ast::Constant::Null) =>
                panic!("null (as a constant) Nullable is not supported yet"),
            ast::ExprKind::UnaryOp(expr, ast::UnaryOperator::Neg)
                if matches!(expr.kind, ast::ExprKind::Constant(ast::Constant::Integer(..))) => {
                let ast::ExprKind::Constant(ast::Constant::Integer(int)) = expr.kind else {
                    unreachable!()
                };
                self.check_expr_integer(int, Negative, expected)
            }
            ast::ExprKind::BinOp(binop) =>
                self.check_expr_binop(binop, expr.span.clone(), expected),
            ast::ExprKind::UnaryOp(expr, unop) => 
                self.check_expr_unary(*unop, expr, expected),
            ast::ExprKind::Name(name) =>
                self.check_expr_name(name),
            ast::ExprKind::Block(stmts) =>
                self.check_expr_block(stmts, expr.node_id, expected),
            ast::ExprKind::Err =>
                Ty::new_error(self.tcx),
            ast::ExprKind::FunctionCall(expr, args, _) =>
                self.check_expr_call(expr, args, expr.span.clone()),
            _ => todo!("typecheck every kind of expression")
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
        let ty = self.check_expr(&expr, expected);

        if let Expectation::Coerce(expected) = expectation {
            self.maybe_emit_type_error(ty, expected, expr.span.clone());
        }

        self.ty_assoc(expr.node_id, ty);
        ty
    }

    fn check_return_ty(&mut self, expr: &'tcx ast::Expr, ret_ty: Ty<'tcx>, ret_ty_span: Range<usize>) {
        self.outer_rib = Some(Rib {
            kind: RibKind::Block,
            owner: expr.node_id,
            expected_ty: Some(ret_ty)
        });

        let ty = self.check_expr(&expr, Some(ret_ty));
        self.maybe_emit_type_error(ty, ret_ty, ret_ty_span);

        if matches!(ret_ty, Ty(types::TyKind::Primitive(types::Primitive::Void))) &&
            matches!(ty, Ty(types::TyKind::Never)) {
            self.diagnostics.warning("unnecessarry return in void function")
                .with_pos(expr.span.end);
        }

        self.ty_assoc(expr.node_id, ty); 
    }

    fn maybe_emit_type_error(&self, found: Ty<'tcx>, expected: Ty<'tcx>, span: Range<usize>) -> Ty<'tcx> {
        if found != expected {
            self.diagnostics.error(format!("mismatched types: expected {expected}, found {found}"))
                .with_span(span);
            return Ty::new_error(self.tcx);
        }
        found
    }
}

struct LoweringCtxt<'tcx> {
    tcx: TyCtxt<'tcx>
}

impl<'tcx> LoweringCtxt<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx }
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

                        let cap = if let ast::ArrayCapacity::Discrete(expr) = cap {
                            todo!("figure out what to do with constants");
                        } else {
                            self.tcx.mk_const_from_inner(ConstInner::Infer)
                        };

                        Ty::new_array(self.tcx, ty, cap)
                    },
                    ast::ArrayCapacity::Dynamic => {
                        let ty = self.lower_ty(ty);
                        Ty::new_dyn_array(self.tcx, ty)
                    }
                }
            }
            ast::TypeExprKind::Generic(..) => panic!("lowering generic types is not supported yet")
        }
    }
}

pub fn type_of(tcx: TyCtxt<'_>, def_id: DefId) -> Ty<'_> {
    todo!()
}

pub struct TypecheckResults;

pub fn typecheck(tcx: TyCtxt<'_>, def_id: DefId) -> &'_ TypecheckResults {
    assert_eq!(def_id.file, interface::INPUT_FILE_IDX, "single-file compiler");

    let node = tcx.node_by_def_id(def_id);

    let body = node.body()
        .expect("typecheck on node without a body");

    let mut ctxt = TypecheckCtxt::new(tcx);

    if let Some(ast::FnSignature { returns, .. }) = node.signature() {
        let sig = tcx.fn_sig(def_id);
        for param in sig.params {
            ctxt.ty_assoc(param.node_id, param.ty);
        }
        ctxt.check_return_ty(body.body, sig.returns, returns.span.clone());
    } else {
        todo!("typecheck non-function items")
    }

    &TypecheckResults
}

pub fn fn_sig(tcx: TyCtxt<'_>, def_id: DefId) -> types::Signature {
    let node = tcx.node_by_def_id(def_id);
    let ctxt = LoweringCtxt::new(tcx);

    match node {
        ast::Node::Item(ast::Item { kind: ast::ItemKind::Function(func), ident, .. }) => {
            let returns = ctxt.lower_ty(&func.sig.returns);

            let mut params = Vec::new();
            for param in &func.sig.params {
                let ty = ctxt.lower_ty(&param.ty);
                let name = match &param.pat.kind {
                    ast::PatternKind::Ident(ident) => ident.symbol,
                    _ => unreachable!()
                };
                params.push(types::Param {
                    name,
                    ty,
                    node_id: param.node_id
                });
            }
            let params: Box<[types::Param]> = params.into_boxed_slice();
            let params: &'_ [types::Param] = tcx.alloc(params);

            types::Signature { returns, params, name: ident.symbol }
        }
        _ => {
            panic!("non-function definition in fn_sig")
        }
    }
}
