
use crate::ast::{SourceFile, Item, ItemKind, Function, Stmt, TypeExpr, Param, GenericParam, FieldDef, Expr, StmtKind, Pattern, ExprKind, FunctionArgument, TypeInit, Constant, QName, PatternKind, GenericParamKind, TypeExprKind, GenericArgument, ControlFlow, self, VariantDef};

pub trait NodeVisitor: Sized {
    fn visit(&self, tree: &SourceFile) {
        visit_vec(&tree.items, |item| self.visit_item(item));
    }

    fn visit_item(&self, item: &Item) {
        noop_visit_item_kind(&item.kind, self);
    }
 
    fn visit_stmt(&self, stmt: &Stmt) {
        noop_visit_stmt_kind(&stmt.kind, self);
    }

    fn visit_param(&self, param: &Param) {
        noop_visit_param(param, self);
    }

    fn visit_field_def(&self, field_def: &FieldDef) {
        self.visit_ty_expr(&field_def.ty);
        visit_option(&field_def.default_init, |default_init| self.visit_expr(default_init));
    }
    
    fn visit_variant_def(&self, variant_def: &VariantDef) {
        visit_option(&variant_def.sset, |sset| self.visit_expr(sset));
    }

    fn visit_expr(&self, expr: &Expr) {
        noop_visit_expr_kind(&expr.kind, self);
    }

    fn visit_argument(&self, arg: &FunctionArgument) {
        noop_visit_argument(arg, self);
    }

    fn visit_generic_argument(&self, arg: &GenericArgument) {
        noop_visit_generic_argument(arg, self);
    }

    fn visit_type_init(&self, init: &TypeInit) {
        let expr = match init {
            TypeInit::Field(_, expr) => expr,
            TypeInit::Direct(expr) => expr,
        };
        self.visit_expr(expr);
    }

    fn visit_generic_param(&self, param: &GenericParam) {
        noop_visit_generic_param_kind(&param.kind, self);
    }

    fn visit_ty_expr(&self, ty: &TypeExpr) {
        noop_visit_ty_expr_kind(&ty.kind, self);
    }

    fn visit_pattern(&self, pattern: &Pattern) {
        noop_visit_pattern_kind(&pattern.kind, self);
    }

    fn visit_const(&self, cnst: &Constant) {
        noop(cnst);
    }

    fn visit_name(&self, name: &QName) {
        noop(name);
    }

    fn visit_control_flow(&self, control_flow: &ControlFlow) {
        noop(control_flow);
    }
}

#[inline]
pub fn visit_vec<T, F: Fn(&T)>(elems: &Vec<T>, visit_elem: F) {
    for elem in elems {
        visit_elem(elem);
    }

}

#[inline]
pub fn visit_option<T, F: Fn(&T)>(option: &Option<T>, visit_val: F) {
    if let Some(val) = option {
        visit_val(val);
    }
}

pub fn noop_visit_item_kind<T: NodeVisitor>(item_kind: &ItemKind, vis: &T) {
    match item_kind {
        ItemKind::Function(func) => {
            visit_fn(func, vis);
        }
        ItemKind::Struct(stc) => {
            visit_vec(&stc.generics, |generic| vis.visit_generic_param(generic));
            visit_vec(&stc.fields, |field_def| vis.visit_field_def(field_def));
        }
        ItemKind::Enum(en) => {
            visit_option(&en.extends, |extends| vis.visit_ty_expr(extends));
            visit_vec(&en.variants, |variant_def| vis.visit_variant_def(variant_def));
        }
        ItemKind::GlobalVar(ty, expr, _) => {
            vis.visit_ty_expr(ty);
            visit_option(expr, |expr| vis.visit_expr(expr));
        }
        ItemKind::Err => ()
    }
}

pub fn visit_fn<T: NodeVisitor>(func: &Function, vis: &T) {
    vis.visit_ty_expr(&func.sig.returns);
    visit_vec(&func.sig.params, |p| vis.visit_param(p));
    visit_vec(&func.sig.generics, |generic| vis.visit_generic_param(generic));
    visit_option(&func.body, |body| vis.visit_expr(body));
}

pub fn noop_visit_stmt_kind<T: NodeVisitor>(stmt_kind: &StmtKind, vis: &T) {
    match stmt_kind {
        StmtKind::Expr(expr) => vis.visit_expr(expr),
        StmtKind::Assign(lhs, rhs) => {
            vis.visit_expr(lhs);
            vis.visit_expr(rhs);
        }
        StmtKind::If(condition, if_body, else_body) => {
            vis.visit_expr(condition);
            visit_vec(if_body, |stmt| vis.visit_stmt(stmt));
            visit_option(else_body, |else_body| vis.visit_stmt(else_body));
        }
        StmtKind::While(condition, body) => {
            vis.visit_expr(condition);
            visit_vec(body, |stmt| vis.visit_stmt(stmt));
        }
        StmtKind::For(var, iterator, body) => {
            vis.visit_pattern(var);
            vis.visit_expr(iterator);
            visit_vec(body, |stmt| vis.visit_stmt(stmt));
        }
        StmtKind::Local(var, ty, init) => {
            vis.visit_pattern(var);
            visit_option(ty, |ty| vis.visit_ty_expr(ty));
            visit_option(init, |init| vis.visit_expr(init));
        }
        StmtKind::Return(expr) => {
            visit_option(expr, |expr| vis.visit_expr(expr));
        }
        StmtKind::ControlFlow(cf) => vis.visit_control_flow(cf),
        StmtKind::Err => ()
    }
}

pub fn noop_visit_expr_kind<T: NodeVisitor>(expr_kind: &ExprKind, vis: &T) {
    match expr_kind {
        ExprKind::BinOp(binop) => {
            vis.visit_expr(&binop.lhs);
            vis.visit_expr(&binop.rhs);
        }
        ExprKind::UnaryOp(base, _) => vis.visit_expr(base),
        ExprKind::Cast(expr, ty, _) => {
            vis.visit_expr(expr);
            visit_option(ty, |ty| vis.visit_ty_expr(ty));
        }
        ExprKind::FunctionCall(base, args, generic_args) => {
            vis.visit_expr(base);
            visit_vec(args, |arg| vis.visit_argument(arg));
            visit_vec(generic_args, |arg| vis.visit_generic_argument(arg));
        }
        ExprKind::TypeInit(ty, inits) => {
            visit_option(ty, |ty| vis.visit_ty_expr(ty));
            visit_vec(inits, |init| vis.visit_type_init(init));
        }
        ExprKind::Subscript(base, args) => {
            vis.visit_expr(base);
            visit_vec(args, |arg| vis.visit_expr(arg));
        }
        ExprKind::Field(base, _) => vis.visit_expr(base),
        ExprKind::Constant(cnst) => vis.visit_const(cnst),
        ExprKind::String(_) => (),
        ExprKind::Name(name) => vis.visit_name(name),
        ExprKind::Tuple(items) =>
            visit_vec(items, |item| vis.visit_expr(item)),
        ExprKind::ShorthandEnum(_) => (),
        ExprKind::Range(start, end, _) => {
            vis.visit_expr(start);
            vis.visit_expr(end);
        }
        ExprKind::Deref(expr) => vis.visit_expr(expr),
        ExprKind::Block(stmts) => visit_vec(stmts, |stmt| vis.visit_stmt(stmt)),
        ExprKind::Err => ()
    }
}

pub fn noop_visit_generic_param_kind<T: NodeVisitor>(gp_kind: &GenericParamKind, vis: &T) {
    match gp_kind {
        GenericParamKind::Type(tys) =>
            visit_vec(tys, |ty| vis.visit_ty_expr(ty)),
        GenericParamKind::Const(cnst) => vis.visit_ty_expr(cnst)
    }
}


pub fn noop_visit_pattern_kind<T: NodeVisitor>(pat_kind: &PatternKind, vis: &T) {
    match pat_kind {
        PatternKind::Tuple(pats) =>
            visit_vec(pats, |pat| vis.visit_pattern(pat)),
        PatternKind::Literal(expr) => vis.visit_expr(expr),
        PatternKind::Ident(_) => (),
    }
}

pub fn noop_visit_ty_expr_kind<T: NodeVisitor>(ty_kind: &TypeExprKind, vis: &T) {
    match ty_kind {
        TypeExprKind::Ref(ty) => vis.visit_ty_expr(ty),
        TypeExprKind::Name(name) => vis.visit_name(name),
        TypeExprKind::Generic(name, args) => {
            vis.visit_name(name);
            visit_vec(args, |arg| vis.visit_generic_argument(arg));
        }
        TypeExprKind::Array(base, cap) => {
            vis.visit_ty_expr(base);
            match cap {
                ast::ArrayCapacity::Discrete(expr) =>
                    vis.visit_expr(expr),
                ast::ArrayCapacity::Infer | ast::ArrayCapacity::Dynamic => ()
            }
        }
        TypeExprKind::Slice(base) =>
            vis.visit_ty_expr(base)
    }
}

pub fn noop_visit_argument<T: NodeVisitor>(arg: &FunctionArgument, vis: &T) {
    match arg {
        FunctionArgument::Direct(expr) => vis.visit_expr(expr),
        FunctionArgument::Keyword(_, expr) => vis.visit_expr(expr)
    }
}

pub fn noop_visit_generic_argument<T: NodeVisitor>(arg: &GenericArgument, vis: &T) {
    match arg {
        GenericArgument::Ty(expr) => vis.visit_ty_expr(expr),
        GenericArgument::Expr(expr) => vis.visit_expr(expr),
        GenericArgument::Constant(cnst) => vis.visit_const(cnst),
    }
}

pub fn noop_visit_param<T: NodeVisitor>(param: &Param, vis: &T) {
    vis.visit_pattern(&param.pat);
    vis.visit_ty_expr(&param.ty);
}

fn noop<T>(_v: T) {}
