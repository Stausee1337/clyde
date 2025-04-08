
use crate::ast::{self, Block, Constant, ControlFlow, Expr, ExprKind, FieldDef, Function, FunctionArgument, GenericArgument, GenericParam, GenericParamKind, Ident, Item, ItemKind, Name, NestedConst, Param, SourceFile, Stmt, StmtKind, TypeExpr, TypeExprKind, TypeInitKind, VariantDef};


pub trait Visitor: Sized {
    fn visit(&mut self, tree: &SourceFile) {
        visit_slice(&tree.items, |item| self.visit_item(item));
    }

    fn visit_item(&mut self, item: &Item) {
        noop_visit_item_kind(&item.kind, self);
    }
 
    fn visit_stmt(&mut self, stmt: &Stmt) {
        noop_visit_stmt_kind(&stmt.kind, self);
    }

    fn visit_param(&mut self, param: &Param) {
        noop_visit_param(param, self);
    }

    fn visit_field_def(&mut self, field_def: &FieldDef) {
        self.visit_ty_expr(&field_def.ty);
        visit_option(field_def.default_init, |default_init| self.visit_expr(default_init));
    }
    
    fn visit_variant_def(&mut self, variant_def: &VariantDef) {
        visit_option(variant_def.sset, |sset| self.visit_expr(sset));
    }

    fn visit_expr(&mut self, expr: &Expr) {
        noop_visit_expr_kind(&expr.kind, self);
    }

    fn visit_nested_const(&mut self, expr: &NestedConst) {
        self.visit_expr(&expr.expr);
    }

    fn visit_argument(&mut self, arg: &FunctionArgument) {
        noop_visit_argument(arg, self);
    }

    fn visit_generic_argument(&mut self, arg: &GenericArgument) {
        noop_visit_generic_argument(arg, self);
    }

    fn visit_type_init(&mut self, init: &TypeInitKind) {
        match init {
            TypeInitKind::Field(_, expr) =>
                self.visit_expr(expr),
            TypeInitKind::Direct(expr) =>
                self.visit_expr(expr)
        }
    }

    fn visit_generic_param(&mut self, param: &GenericParam) {
        noop_visit_generic_param_kind(&param.kind, self);
    }

    fn visit_ty_expr(&mut self, ty: &TypeExpr) {
        noop_visit_ty_expr_kind(&ty.kind, self);
    }

    fn visit_block(&mut self, block: &Block) {
        visit_slice(&block.stmts, |stmt| self.visit_stmt(stmt));
    }

    fn visit_const(&mut self, cnst: &Constant) {
        noop(cnst);
    }

    fn visit_name(&mut self, name: &Name) {
        noop(name);
    }

    fn visit_control_flow(&mut self, control_flow: &ControlFlow) {
        noop(control_flow);
    }
}

#[inline]
pub fn visit_slice<T, F: FnMut(&T)>(elems: &[T], mut visit_elem: F) {
    for elem in elems {
        visit_elem(elem);
    }

}

#[inline]
pub fn visit_option<T, F: FnMut(&T)>(option: Option<&T>, mut visit_val: F) {
    if let Some(val) = option {
        visit_val(val);
    }
}

pub fn noop_visit_item_kind<T: Visitor>(item_kind: &ItemKind, vis: &mut T) {
    match item_kind {
        ItemKind::Function(func) => {
            visit_fn(func, vis);
        }
        ItemKind::Struct(stc) => {
            visit_slice(&stc.generics, |generic| vis.visit_generic_param(generic));
            visit_slice(&stc.fields, |field_def| vis.visit_field_def(field_def));
        }
        ItemKind::Enum(en) => {
            visit_option(en.extends, |extends| vis.visit_ty_expr(extends));
            visit_slice(&en.variants, |variant_def| vis.visit_variant_def(variant_def));
        }
        ItemKind::GlobalVar(global_var) => {
            vis.visit_ty_expr(global_var.ty);
            visit_option(global_var.init, |init| vis.visit_expr(init));
        }
        ItemKind::Err => ()
    }
}

pub fn visit_fn<T: Visitor>(func: &Function, vis: &mut T) {
    vis.visit_ty_expr(&func.sig.returns);
    visit_slice(&func.sig.params, |p| vis.visit_param(p));
    visit_slice(&func.sig.generics, |generic| vis.visit_generic_param(generic));
    visit_option(func.body, |body| vis.visit_expr(body));
}

pub fn noop_visit_stmt_kind<T: Visitor>(stmt_kind: &StmtKind, vis: &mut T) {
    match stmt_kind {
        StmtKind::Expr(expr) => vis.visit_expr(expr),
        StmtKind::If(if_stmt) => {
            vis.visit_expr(if_stmt.condition);
            vis.visit_block(&if_stmt.body);
            visit_option(if_stmt.else_branch, |else_body| vis.visit_stmt(else_body));
        }
        StmtKind::While(while_loop) => {
            vis.visit_expr(while_loop.condition);
            vis.visit_block(&while_loop.body);
        }
        StmtKind::For(for_loop) => {
            vis.visit_expr(for_loop.iterator);
            vis.visit_block(&for_loop.body);
        }
        StmtKind::Local(local) => {
            visit_option(local.ty, |ty| vis.visit_ty_expr(ty));
            visit_option(local.init, |init| vis.visit_expr(init));
        }
        StmtKind::Return(expr) => {
            visit_option(*expr, |expr| vis.visit_expr(expr));
        }
        StmtKind::ControlFlow(cf) => vis.visit_control_flow(cf),
        StmtKind::Block(block) => vis.visit_block(block),
        StmtKind::Err => ()
    }
}

pub fn noop_visit_expr_kind<T: Visitor>(expr_kind: &ExprKind, vis: &mut T) {
    match expr_kind {
        ExprKind::BinaryOp(binop) => {
            vis.visit_expr(&binop.lhs);
            vis.visit_expr(&binop.rhs);
        }
        ExprKind::AssignOp(assign) => {
            vis.visit_expr(assign.lhs);
            vis.visit_expr(assign.rhs);
        }
        ExprKind::UnaryOp(unaryop) => vis.visit_expr(unaryop.expr),
        ExprKind::Cast(cast) => {
            vis.visit_expr(cast.expr);
            visit_option(cast.ty, |ty| vis.visit_ty_expr(ty));
        }
        ExprKind::FunctionCall(call) => {
            vis.visit_expr(call.callable);
            visit_slice(call.args, |arg| vis.visit_argument(arg));
            visit_slice(call.generic_args, |arg| vis.visit_generic_argument(arg));
        }
        ExprKind::TypeInit(init) => {
            visit_option(init.ty, |ty| vis.visit_ty_expr(ty));
            visit_slice(init.initializers, |init| vis.visit_type_init(init));
        }
        ExprKind::Subscript(subscript) => {
            vis.visit_expr(subscript.expr);
            visit_slice(subscript.args, |arg| vis.visit_expr(arg));
        }
        ExprKind::Field(field) => vis.visit_expr(field.expr),
        ExprKind::Constant(cnst) => vis.visit_const(cnst),
        ExprKind::String(_) => (),
        ExprKind::Name(name) => vis.visit_name(name),
        ExprKind::Tuple(items) =>
            visit_slice(items, |item| vis.visit_expr(item)),
        // ExprKind::ShorthandEnum(_) => (),
        // ExprKind::EnumVariant(ty, _) => vis.visit_ty_expr(ty),
        ExprKind::Range(range) => {
            vis.visit_expr(range.start);
            vis.visit_expr(range.end);
        }
        ExprKind::Deref(expr) => vis.visit_expr(expr),
        ExprKind::Block(block) => vis.visit_block(block),
        ExprKind::Err => ()
    }
}

pub fn noop_visit_generic_param_kind<T: Visitor>(gp_kind: &GenericParamKind, vis: &mut T) {
    match gp_kind {
        GenericParamKind::Type(tys) =>
            visit_slice(*tys, |ty| vis.visit_ty_expr(ty)),
        GenericParamKind::Const(cnst) => vis.visit_ty_expr(cnst)
    }
}

pub fn noop_visit_ty_expr_kind<T: Visitor>(ty_kind: &TypeExprKind, vis: &mut T) {
    match ty_kind {
        TypeExprKind::Ref(ty) => vis.visit_ty_expr(ty),
        TypeExprKind::Name(name) => vis.visit_name(name),
        TypeExprKind::Generic(generic) => {
            vis.visit_name(&generic.name);
            visit_slice(generic.args, |arg| vis.visit_generic_argument(arg));
        }
        TypeExprKind::Array(array) => {
            vis.visit_ty_expr(array.ty);
            match array.cap {
                ast::ArrayCapacity::Discrete(ref expr) =>
                    vis.visit_nested_const(expr),
                ast::ArrayCapacity::Infer | ast::ArrayCapacity::Dynamic => ()
            }
        }
        TypeExprKind::Slice(base) =>
            vis.visit_ty_expr(base),
        TypeExprKind::Tuple(tys) =>
            visit_slice(tys, |ty| vis.visit_ty_expr(ty))
    }
}

pub fn noop_visit_argument<T: Visitor>(arg: &FunctionArgument, vis: &mut T) {
    match arg {
        FunctionArgument::Direct(expr) => vis.visit_expr(expr),
        FunctionArgument::Keyword(_, expr) => vis.visit_expr(expr)
    }
}

pub fn noop_visit_generic_argument<T: Visitor>(arg: &GenericArgument, vis: &mut T) {
    match arg {
        GenericArgument::Ty(expr) => vis.visit_ty_expr(expr),
        GenericArgument::Expr(expr) => vis.visit_nested_const(expr),
        GenericArgument::Constant(cnst) => vis.visit_const(cnst),
    }
}

pub fn noop_visit_param<T: Visitor>(param: &Param, vis: &mut T) {
    vis.visit_ty_expr(&param.ty);
}

fn noop<T>(_v: T) {}
