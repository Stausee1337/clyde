use std::ptr;

use crate::ast::{SourceFile, Item, ItemKind, Function, Stmt, TypeExpr, Param, GenericParam, FieldDef, Expr, StmtKind, Pattern, ExprKind, FunctionArgument, TypeInit, Constant, QName, PatternKind, GenericParamKind, TypeExprKind, GenericArgument, ControlFlow, self, VariantDef};


pub trait MutVisitor: Sized {
    fn visit(&mut self, tree: &mut SourceFile) {
        visit_vec(&mut tree.items, |item| self.visit_item(item));
    }

    fn visit_item(&mut self, item: &mut Item) {
        noop_visit_item_kind(&mut item.kind, self);
    }
 
    fn visit_stmt(&mut self, stmt: &mut Stmt) {
        noop_visit_stmt_kind(&mut stmt.kind, self);
    }

    fn visit_param(&mut self, param: &mut Param) {
        noop_visit_param(param, self);
    }

    fn visit_field_def(&mut self, field_def: &mut FieldDef) {
        self.visit_ty_expr(&mut field_def.ty);
        visit_option(&mut field_def.default_init, |default_init| self.visit_expr(default_init));
    }
    
    fn visit_variant_def(&mut self, variant_def: &mut VariantDef) {
        visit_option(&mut variant_def.sset, |sset| self.visit_expr(sset));
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        noop_visit_expr_kind(&mut expr.kind, self);
    }

    fn visit_argument(&mut self, arg: &mut FunctionArgument) {
        noop_visit_argument(arg, self);
    }

    fn visit_generic_argument(&mut self, arg: &mut GenericArgument) {
        noop_visit_generic_argument(arg, self);
    }

    fn visit_type_init(&mut self, init: &mut TypeInit) {
        let expr = match init {
            TypeInit::Field(_, expr) => expr,
            TypeInit::Direct(expr) => expr,
        };
        self.visit_expr(expr);
    }

    fn visit_generic_param(&mut self, param: &mut GenericParam) {
        noop_visit_generic_param_kind(&mut param.kind, self);
    }

    fn visit_ty_expr(&mut self, ty: &mut TypeExpr) {
        noop_visit_ty_expr_kind(&mut ty.kind, self);
    }

    fn visit_pattern(&mut self, pattern: &mut Pattern) {
        noop_visit_pattern_kind(&mut pattern.kind, self);
    }

    fn visit_const(&mut self, cnst: &mut Constant) {
        noop(cnst);
    }

    fn visit_name(&mut self, name: &mut QName) {
        noop(name);
    }

    fn visit_control_flow(&mut self, control_flow: &mut ControlFlow) {
        noop(control_flow);
    }
}

#[inline]
pub fn visit_vec<T, F: FnMut(&mut T)>(elems: &mut Vec<T>, mut visit_elem: F) {
    for elem in elems {
        visit_elem(elem);
    }

}

#[inline]
pub fn visit_option<T, F: FnMut(&mut T)>(option: &mut Option<T>, mut visit_val: F) {
    if let Some(val) = option {
        visit_val(val);
    }
}

#[inline]
pub fn map_vec<T, I: IntoIterator<Item = T>, F: FnMut(T) -> I>(elems: &mut Vec<T>, mut f: F) {
    let mut len = elems.len();
    let mut read_i = 0;
    let mut write_i = 0;
    unsafe {
        while read_i < len {
            let e = ptr::read(elems.as_mut_ptr().add(read_i));
            read_i += 1;

            let iter = f(e);
            for e in iter {
                if write_i < read_i {
                    ptr::write(elems.as_mut_ptr().add(write_i), e);
                    write_i += 1;
                } else {
                    elems.insert(write_i, e);
                    len = elems.len();

                    read_i += 1;
                    write_i += 1;
                }
            }
        }
        elems.set_len(write_i);
    }
}

pub fn noop_visit_item_kind<T: MutVisitor>(item_kind: &mut ItemKind, vis: &mut T) {
    match item_kind {
        ItemKind::Function(func) => {
            visit_fn(func, vis);
        }
        ItemKind::Struct(stc) => {
            visit_vec(&mut stc.generics, |generic| vis.visit_generic_param(generic));
            visit_vec(&mut stc.fields, |field_def| vis.visit_field_def(field_def));
        }
        ItemKind::Enum(en) => {
            visit_option(&mut en.extends, |extends| vis.visit_ty_expr(extends));
            visit_vec(&mut en.variants, |variant_def| vis.visit_variant_def(variant_def));
        }
        ItemKind::GlobalVar(ty, expr, _) => {
            vis.visit_ty_expr(ty);
            visit_option(expr, |expr| vis.visit_expr(expr));
        }
        ItemKind::Err => ()
    }
}

pub fn visit_fn<T: MutVisitor>(func: &mut Function, vis: &mut T) {
    vis.visit_ty_expr(&mut func.sig.returns);
    visit_vec(&mut func.sig.params, |p| vis.visit_param(p));
    visit_vec(&mut func.sig.generics, |generic| vis.visit_generic_param(generic));
    visit_option(&mut func.body, |body| vis.visit_expr(body));
}

pub fn noop_visit_stmt_kind<T: MutVisitor>(stmt_kind: &mut StmtKind, vis: &mut T) {
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

pub fn noop_visit_expr_kind<T: MutVisitor>(expr_kind: &mut ExprKind, vis: &mut T) {
    match expr_kind {
        ExprKind::BinOp(binop) => {
            vis.visit_expr(&mut binop.lhs);
            vis.visit_expr(&mut binop.rhs);
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
        ExprKind::Attribute(base, _) => vis.visit_expr(base),
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

pub fn noop_visit_generic_param_kind<T: MutVisitor>(gp_kind: &mut GenericParamKind, vis: &mut T) {
    match gp_kind {
        GenericParamKind::Type(tys) =>
            visit_vec(tys, |ty| vis.visit_ty_expr(ty)),
        GenericParamKind::Const(cnst) => vis.visit_ty_expr(cnst)
    }
}


pub fn noop_visit_pattern_kind<T: MutVisitor>(pat_kind: &mut PatternKind, vis: &mut T) {
    match pat_kind {
        PatternKind::Tuple(pats) =>
            visit_vec(pats, |pat| vis.visit_pattern(pat)),
        PatternKind::Literal(expr) => vis.visit_expr(expr),
        PatternKind::Ident(_) => (),
    }
}

pub fn noop_visit_ty_expr_kind<T: MutVisitor>(ty_kind: &mut TypeExprKind, vis: &mut T) {
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
    }
}

pub fn noop_visit_argument<T: MutVisitor>(arg: &mut FunctionArgument, vis: &mut T) {
    match arg {
        FunctionArgument::Direct(expr) => vis.visit_expr(expr),
        FunctionArgument::Keyword(_, expr) => vis.visit_expr(expr)
    }
}

pub fn noop_visit_generic_argument<T: MutVisitor>(arg: &mut GenericArgument, vis: &mut T) {
    match arg {
        GenericArgument::Ty(expr) => vis.visit_ty_expr(expr),
        GenericArgument::Expr(expr) => vis.visit_expr(expr),
        GenericArgument::Constant(cnst) => vis.visit_const(cnst),
    }
}

pub fn noop_visit_param<T: MutVisitor>(param: &mut Param, vis: &mut T) {
    vis.visit_pattern(&mut param.pat);
    vis.visit_ty_expr(&mut param.ty);
}

fn noop<T>(_v: T) {}
