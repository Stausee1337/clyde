use std::collections::HashMap;

use crate::{context::TyCtxt, types::{Ty, Const, ConstInner, Primitive, TyKind, NumberSign}, ast::{DefId, self, DefinitionKind}, interface};

struct TypecheckCtxt<'tcx> {
    tcx: TyCtxt<'tcx>,
    associations: HashMap<ast::NodeId, Ty<'tcx>, ahash::RandomState>,
}

impl<'tcx> TypecheckCtxt<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx, associations: Default::default() }
    }

    fn lower_const(&self, _cnst: &ast::Expr) -> Const<'tcx> {
        // It's going to be more complicated than that.
        // Any global definiton needs tobe resolved 
        // a using query(DefId) -> Const.
        // It'll need much of the similar logic from 
        // this function here
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

    fn check_expr_kind(&mut self, expr_kind: &'tcx ast::ExprKind, expected: Option<Ty<'tcx>>) -> Ty<'tcx> {
        use NumberSign::*;
        match expr_kind {
            ast::ExprKind::String(..) => 
                Ty::new_primitive(self.tcx, Primitive::String),
            ast::ExprKind::Constant(ast::Constant::Boolean(..)) =>
                Ty::new_primitive(self.tcx, Primitive::Bool),
            ast::ExprKind::Constant(ast::Constant::Integer(int)) =>
                self.check_expr_integer(*int, Positive, expected),
            ast::ExprKind::Constant(ast::Constant::Null) =>
                panic!("null is not supported yet"),
            ast::ExprKind::UnaryOp(expr, ast::UnaryOperator::Neg)
                if matches!(expr.kind, ast::ExprKind::Constant(ast::Constant::Integer(..))) => {
                let ast::ExprKind::Constant(ast::Constant::Integer(int)) = expr.kind else {
                    unreachable!()
                };
                self.check_expr_integer(int, Negative, expected)
            },
            ast::ExprKind::Name(name) =>
                self.check_expr_name(name),
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

    fn check_expr_with_expectation(&mut self, expr: &'tcx ast::Expr, expected: Option<Ty<'tcx>>) {
        let ty = self.check_expr_kind(&expr.kind, expected);

        self.ty_assoc(expr.node_id, ty); 
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

        ctxt.check_expr_with_expectation(body.body, Some(ret_ty));
    } else {
        todo!("typecheck non-function items")
    }

    todo!()
}

