
use crate::syntax::ast::{self, Block, ControlFlow, Expr, ExprKind, FieldDef, Function, FunctionArgument, GenericArgument, GenericArgumentKind, GenericParam, GenericParamKind, Import, Item, ItemKind, Literal, NestedConst, Param, Path, PathSegment, SourceFile, Stmt, StmtKind, TypeExpr, TypeExprKind, TypeInitKind, VariantDef};


pub trait Visitor<'tcx>: Sized {
    fn visit(&mut self, tree: &'tcx SourceFile<'tcx>);

    fn visit_import(&mut self, import: &'tcx Import) {
        noop(import);
    }

    fn visit_item(&mut self, item: &'tcx Item<'tcx>) {
        noop_visit_item_kind(&item.kind, self);
    }
 
    fn visit_stmt(&mut self, stmt: &'tcx Stmt<'tcx>) {
        noop_visit_stmt_kind(&stmt.kind, self);
    }

    fn visit_param(&mut self, param: &'tcx Param<'tcx>) {
        noop_visit_param(param, self);
    }

    fn visit_field_def(&mut self, field_def: &'tcx FieldDef<'tcx>) {
        self.visit_ty_expr(&field_def.ty);
        visit_option(field_def.default_init, |default_init| self.visit_expr(default_init));
    }
    
    fn visit_variant_def(&mut self, variant_def: &'tcx VariantDef<'tcx>) {
        visit_option(variant_def.sset, |sset| self.visit_nested_const(sset));
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        noop_visit_expr_kind(&expr.kind, self);
    }

    fn visit_nested_const(&mut self, expr: &'tcx NestedConst<'tcx>) {
        self.visit_expr(&expr.expr);
    }

    fn visit_argument(&mut self, arg: &'tcx FunctionArgument<'tcx>) {
        noop_visit_argument(arg, self);
    }

    fn visit_generic_argument(&mut self, arg: &'tcx GenericArgument<'tcx>) {
        noop_visit_generic_argument(arg, self);
    }

    fn visit_type_init(&mut self, init: &'tcx TypeInitKind<'tcx>) {
        match init {
            TypeInitKind::Field(_, expr) =>
                self.visit_expr(expr),
            TypeInitKind::Direct(expr) =>
                self.visit_expr(expr)
        }
    }

    fn visit_generic_param(&mut self, param: &'tcx GenericParam<'tcx>) {
        noop_visit_generic_param_kind(&param.kind, self);
    }

    fn visit_ty_expr(&mut self, ty: &'tcx TypeExpr<'tcx>) {
        noop_visit_ty_expr_kind(&ty.kind, self);
    }

    fn visit_block(&mut self, block: &'tcx Block<'tcx>) {
        visit_slice(&block.stmts, |stmt| self.visit_stmt(stmt));
    }

    fn visit_literal(&mut self, cnst: &'tcx Literal) {
        noop(cnst);
    }

    fn visit_path(&mut self, path: &'tcx Path<'tcx>) {
        visit_slice(path.segments, |segment| self.visit_path_segment(segment));
    }

    fn visit_path_segment(&mut self, segment: &'tcx PathSegment<'tcx>) {
        visit_slice(segment.generic_args, |arg| self.visit_generic_argument(arg));
    }

    fn visit_control_flow(&mut self, control_flow: &'tcx ControlFlow) {
        noop(control_flow);
    }
}

#[inline]
pub fn visit_slice<'tcx, T, F: FnMut(&'tcx T)>(elems: &'tcx [T], mut visit_elem: F) {
    for elem in elems {
        visit_elem(elem);
    }

}

#[inline]
pub fn visit_option<'tcx, T, F: FnMut(&'tcx T)>(option: Option<&'tcx T>, mut visit_val: F) {
    if let Some(val) = option {
        visit_val(val);
    }
}

pub fn noop_visit_item_kind<'tcx, T: Visitor<'tcx>>(item_kind: &'tcx ItemKind<'tcx>, vis: &mut T) {
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

pub fn visit_fn<'tcx, T: Visitor<'tcx>>(func: &'tcx Function<'tcx>, vis: &mut T) {
    vis.visit_ty_expr(&func.sig.returns);
    visit_slice(&func.sig.params, |p| vis.visit_param(p));
    visit_slice(&func.sig.generics, |generic| vis.visit_generic_param(generic));
    visit_option(func.body, |body| vis.visit_expr(body));
}

pub fn noop_visit_stmt_kind<'tcx, T: Visitor<'tcx>>(stmt_kind: &'tcx StmtKind<'tcx>, vis: &mut T) {
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
        StmtKind::Yeet(yeet) => visit_option(yeet.expr, |expr| vis.visit_expr(expr)),
        StmtKind::Err => ()
    }
}

pub fn noop_visit_expr_kind<'tcx, T: Visitor<'tcx>>(expr_kind: &'tcx ExprKind<'tcx>, vis: &mut T) {
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
        }
        ExprKind::TypeInit(init) => {
            vis.visit_ty_expr(init.ty);
            visit_slice(init.initializers, |init| vis.visit_type_init(init));
        }
        ExprKind::Subscript(subscript) => {
            vis.visit_expr(subscript.expr);
            visit_slice(subscript.args, |arg| vis.visit_expr(arg));
        }
        ExprKind::Field(field) => vis.visit_expr(field.expr),
        ExprKind::Literal(literal) => vis.visit_literal(literal),
        ExprKind::Path(path) => vis.visit_path(path),
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

pub fn noop_visit_generic_param_kind<'tcx, T: Visitor<'tcx>>(gp_kind: &'tcx GenericParamKind<'tcx>, vis: &mut T) {
    match gp_kind {
        GenericParamKind::Type(..) => (),
        GenericParamKind::Const(_, cnst) => vis.visit_ty_expr(cnst),
    }
}

pub fn noop_visit_ty_expr_kind<'tcx, T: Visitor<'tcx>>(ty_kind: &'tcx TypeExprKind<'tcx>, vis: &mut T) {
    match ty_kind {
        TypeExprKind::Ref(ty) => vis.visit_ty_expr(ty),
        TypeExprKind::Path(path) => vis.visit_path(path),
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
        TypeExprKind::Err => ()
    }
}

pub fn noop_visit_argument<'tcx, T: Visitor<'tcx>>(arg: &'tcx FunctionArgument<'tcx>, vis: &mut T) {
    match arg {
        FunctionArgument::Direct(expr) => vis.visit_expr(expr),
        FunctionArgument::Keyword(_, expr) => vis.visit_expr(expr)
    }
}

pub fn noop_visit_generic_argument<'tcx, T: Visitor<'tcx>>(arg: &'tcx GenericArgument<'tcx>, vis: &mut T) {
    match &arg.kind {
        GenericArgumentKind::Ty(expr) => vis.visit_ty_expr(expr),
        GenericArgumentKind::Expr(expr) => vis.visit_nested_const(expr),
        GenericArgumentKind::Literal(cnst) => vis.visit_literal(cnst),
    }
}

pub fn noop_visit_param<'tcx, T: Visitor<'tcx>>(param: &'tcx Param<'tcx>, vis: &mut T) {
    vis.visit_ty_expr(&param.ty);
}

fn noop<T>(_v: T) {}
