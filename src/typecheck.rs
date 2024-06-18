use std::{collections::HashMap, ops::Range};

use crate::{context::TyCtxt, types::{Ty, Const, ConstInner, Primitive, TyKind, NumberSign, self}, ast::{DefId, self, DefinitionKind, ControlFlow}, interface, diagnostics::Diagnostics};

struct Rib<'tcx> {
    kind: RibKind,
    owner: ast::NodeId,
    expected_ty: Option<Ty<'tcx>>
}

#[derive(PartialEq, Eq)]
enum RibKind {
    If, Loop, Block,
}

#[derive(Default)]
struct TypecheckStmtResult<'tcx> {
    result_ty: Option<Ty<'tcx>>,
    // ONLY true if a statement diverges COMPLETELY,
    // and does no longer continue on the applications
    // main path in ANY way!
    // eg. if ... { return ...; } would have this property `true`
    diverges: bool
}

impl<'tcx> TypecheckStmtResult<'tcx> {
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
    associations: HashMap<ast::NodeId, Ty<'tcx>, ahash::RandomState>,
}

impl<'tcx> TypecheckCtxt<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            ribs: Vec::new(),
            outer_rib: None,
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

    fn lower_const(&self, _cnst: &ast::Expr) -> Const<'tcx> {
        // It's going to be more complicated than that.
        // Any global definiton needs to be resolved 
        // using  a query(DefId) -> Const.
        // It'll need much of the similar logic from 
        // this function here.
        // Probably just gonna use this Ctxt again
        todo!()
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
                            self.lower_const(expr)
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
        let lhs_ty = self.check_expr_with_expectation(lhs, None);
        if let Ty(types::TyKind::Never) = self.check_expr_with_expectation(rhs, Some(lhs_ty)) {
            return true;
        }
        false
    }

    fn check_stmt_if(
        &mut self,
        condition: &'tcx ast::Expr, body: &'tcx [ast::Stmt], else_branch: Option<&'tcx ast::Stmt>, owner: ast::NodeId) -> TypecheckStmtResult<'tcx> {
        todo!();
    }

    fn check_stmt_local(&mut self,
        stmt: &'tcx ast::Stmt, expr: Option<&'tcx ast::Expr>, ty: Option<&'tcx ast::TypeExpr>) -> bool {
        let expected = ty.map(|ty| self.lower_ty(&ty));
        if expected.is_none() && expr.is_none() {
            self.diagnostics.error("type-anonymous variable declarations require an init expresssion")
                .with_span(stmt.span.clone());
            self.ty_assoc(stmt.node_id, Ty::new_error(self.tcx));
            return false;
        } else if let Some(expr) = expr {
            let ty = self.check_expr_with_expectation(expr, expected);
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

    fn check_stmt(&mut self, stmt: &'tcx ast::Stmt) -> TypecheckStmtResult<'tcx> {
        match &stmt.kind {
            ast::StmtKind::Expr(expr) => {
                let ty = self.check_expr_with_expectation(expr, None);
                if let Ty(types::TyKind::Never) = ty {
                    return TypecheckStmtResult::never_diverges(self.tcx, true);
                }
            }
            ast::StmtKind::Assign(lhs, rhs) =>
                return TypecheckStmtResult::never_diverges(self.tcx, self.check_stmt_assign(lhs, rhs)),
            ast::StmtKind::If(condition, body, branch) =>
                return self.check_stmt_if(condition, body, branch.as_deref(), stmt.node_id),
            ast::StmtKind::Local(_, ty, expr) =>
                return TypecheckStmtResult::never_diverges(
                    self.tcx, self.check_stmt_local(stmt, expr.as_deref(), ty.as_deref())),
            ast::StmtKind::Return(expr) => {
                let Some(Some(return_ty)) = self.outer_rib.as_ref().map(|rib| rib.expected_ty) else {
                    self.diagnostics.error("`return` found outside of function body")
                        .with_span(stmt.span.clone());
                    self.diagnostics.note("use break ...; for producing values")
                        .with_span(stmt.span.clone());
                    return TypecheckStmtResult::default();
                };
                let ty = expr
                    .as_ref()
                    .map(|expr| self.check_expr_with_expectation(expr, Some(return_ty)));
                let ty = match ty {
                    Some(ty) => ty,
                    None => {
                        let ty = Ty::new_primitive(self.tcx, types::Primitive::Void);
                        self.maybe_emit_type_error(ty, return_ty, stmt.span.clone());
                        ty
                    }
                };
                self.ty_assoc(stmt.node_id, ty);
                return TypecheckStmtResult {
                    diverges: true,
                    result_ty: Some(Ty::new_never(self.tcx))
                };
            }
            ast::StmtKind::ControlFlow(flow) => {
                let Some(lop) = self.find_rib(RibKind::Loop) else {
                    self.diagnostics.error(format!("`{}` found outside of loop", flow.kind))
                        .with_span(stmt.span.clone());
                    return TypecheckStmtResult::default();
                };
                flow.res.set(lop.owner).unwrap();
                return TypecheckStmtResult {
                    result_ty: None,
                    diverges: true
                };
            }
            ast::StmtKind::Err => (),
            _ => todo!("Unimplemented Stmt Kind")
        }
        TypecheckStmtResult::default()
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

    fn check_expr_block(&mut self, stmts: &'tcx [ast::Stmt], owner: ast::NodeId, expected: Option<Ty<'tcx>>) -> Ty<'tcx> {
        self.with_rib(RibKind::Block, owner, expected, |this| {
            let mut iterator = stmts.iter();
            let mut return_ty = None;
            for stmt in &mut iterator {
                let result = this.check_stmt(stmt);
                if result.diverges {
                    return_ty = result.result_ty;
                    break;
                }
            }

            if return_ty.is_some() {
                if let Some(stmt) = iterator.next() {
                    this.diagnostics.warning("this code is unreachable")
                        .with_span(stmt.span.clone());
                }
            }

            return_ty.unwrap_or_else(|| Ty::new_primitive(this.tcx, types::Primitive::Void))
        })
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
            },
            ast::ExprKind::Name(name) =>
                self.check_expr_name(name),
            ast::ExprKind::Block(stmts) =>
                self.check_expr_block(stmts, expr.node_id, expected),
            ast::ExprKind::Err =>
                Ty::new_error(self.tcx),
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

    fn check_expr_with_expectation(&mut self, expr: &'tcx ast::Expr, expected: Option<Ty<'tcx>>) -> Ty<'tcx> {
        let ty = self.check_expr(&expr, expected);

        if let Some(expected) = expected {
            self.maybe_emit_type_error(ty, expected, expr.span.clone());
        }

        self.ty_assoc(expr.node_id, ty);
        ty
    }

    fn check_return_ty(&mut self, expr: &'tcx ast::Expr, ret_ty: Ty<'tcx>) {
        self.outer_rib = Some(Rib {
            kind: RibKind::Block,
            owner: expr.node_id,
            expected_ty: Some(ret_ty)
        });

        let ty = self.check_expr(&expr, Some(ret_ty));

        self.ty_assoc(expr.node_id, ty); 
    }

    fn maybe_emit_type_error(&self, found: Ty<'tcx>, expected: Ty<'tcx>, span: Range<usize>) {
        if found != expected {
            self.diagnostics.error(format!("mismatched types: expected {expected}, found {found}"))
                .with_span(span);
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

    if let Some(sig) = node.signature() {
        // TODO: function signature computation should be it's own query
        for param in sig.params {
            let ty = ctxt.lower_ty(&param.ty);
            ctxt.ty_assoc(param.node_id, ty);
        }
        let ret_ty = ctxt.lower_ty(sig.ret_ty);

        ctxt.check_return_ty(body.body, ret_ty);
    } else {
        todo!("typecheck non-function items")
    }

    &TypecheckResults
}

