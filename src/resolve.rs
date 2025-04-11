
use std::collections::HashMap;

use crate::{ast::{self, DefinitionKind, NodeId, OutsideLoopScope, Resolution}, context::TyCtxt, diagnostics::{DiagnosticsCtxt, Message}, lexer::Span, node_visitor::{self, Visitor}, symbol::Symbol};

/// AST (&tree) 
///     |          |
/// Types & Fn's   |                                |
///          assoc vars, fields, args with types    |
///                                                 |
///                                           Name <-> declaration site (NodeId)

#[derive(Clone, Copy, PartialEq, Eq)]
enum NameSpace {
    Type, Function, Variable 
}

impl std::fmt::Display for NameSpace {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use NameSpace as Sym;
        match self {
            Sym::Type => write!(f, "type"),
            Sym::Function => write!(f, "function"),
            Sym::Variable => write!(f, "variable"),
        }
    }
}

impl From<DefinitionKind> for NameSpace {
    fn from(value: DefinitionKind) -> Self {
        use DefinitionKind as D;
        match value {
            D::Struct | D::Enum => NameSpace::Type,
            D::Function => NameSpace::Function,
            D::Global | D::Const => NameSpace::Variable,
        }
    }
}

#[derive(Clone)]
struct Declaration {
    site: ast::DefId,
    kind: DefinitionKind,
    span: Span,
}

#[derive(Clone)]
struct Local {
    site: ast::NodeId,
    span: Span,
}

struct ResolutionState<'tcx> {
    items: Vec<ast::DefId>,
    diagnostics: &'tcx DiagnosticsCtxt,
    types: HashMap<Symbol, Declaration, ahash::RandomState>,
    functions: HashMap<Symbol, Declaration, ahash::RandomState>,
    globals: HashMap<Symbol, Declaration, ahash::RandomState>,
    declarations: index_vec::IndexVec<ast::DefId, ast::NodeId>
}

#[derive(Debug)]
pub struct ResolutionResults {
    pub items: Vec<ast::DefId>,
    pub entry: Option<ast::DefId>,
    pub declarations: index_vec::IndexVec<ast::DefId, ast::NodeId>
}

impl<'tcx> ResolutionState<'tcx> {
    fn new(diagnostics: &'tcx DiagnosticsCtxt) -> ResolutionState<'tcx> {
        ResolutionState {
            diagnostics,
            items: Default::default(),
            types: Default::default(),
            functions: Default::default(),
            globals: Default::default(),
            declarations: Default::default()
        }
    }

    fn define(&mut self, kind: DefinitionKind, name: ast::Ident, site: ast::NodeId) {
        let space = match kind {
            DefinitionKind::Struct | DefinitionKind::Enum => &mut self.types,
            DefinitionKind::Function => &mut self.functions,
            DefinitionKind::Global | DefinitionKind::Const => &mut self.globals,
        };
        let declaration = Declaration {
            site: self.declarations.push(site).into(), kind, span: name.span
        };
        self.items.push(declaration.site);
        if let Some(prev) = space.insert(name.symbol, declaration) {
            let space: NameSpace = kind.into();
            Message::error(format!("redeclaration of {space} {name:?}", name = name.symbol.get()))
                .at(name.span)
                .hint(format!("previous declaration of {name:?} here", name = name.symbol.get()), prev.span)
                .push(self.diagnostics);
        }
    }

    fn results(self) -> ResolutionResults {
        let entry = self.functions.get(&Symbol::intern("main")).map(|decl| decl.site);
        ResolutionResults {
            items: self.items, entry,
            declarations: self.declarations
        }
    }
}

struct TypeResolutionPass<'r, 'tcx> {
    resolution: &'r mut ResolutionState<'tcx>,
}

impl<'r, 'tcx> TypeResolutionPass<'r, 'tcx> {
    fn new(resolution: &'r mut ResolutionState<'tcx>) -> Self {
        Self { resolution }
    }

    fn resolve(&mut self, tree: &mut ast::SourceFile) {
        self.visit(tree);
    }
}

impl<'r, 'tcx> Visitor for TypeResolutionPass<'r, 'tcx> {
    fn visit_item(&mut self, item: &ast::Item) {
        match &item.kind {
            ast::ItemKind::Struct(stc) => {
                self.resolution.define(DefinitionKind::Struct, item.ident.clone(), item.node_id);
                node_visitor::visit_slice(stc.fields, |field_def| self.visit_field_def(field_def));
                node_visitor::visit_slice(stc.generics, |generic| self.visit_generic_param(generic));
            }, 
            ast::ItemKind::Enum(en) => {
                self.resolution.define(DefinitionKind::Enum, item.ident.clone(), item.node_id);
                node_visitor::visit_slice(en.variants, |variant_def| self.visit_variant_def(variant_def));
            },
            ast::ItemKind::Function(function) => {
                self.resolution.define(DefinitionKind::Function, item.ident.clone(), item.node_id);
                node_visitor::visit_fn(function, self);
            },
            ast::ItemKind::GlobalVar(global) => {
                self.resolution.define(
                    if global.constant {DefinitionKind::Global} else {DefinitionKind::Const},
                    item.ident.clone(), item.node_id);
                self.visit_ty_expr(global.ty);
                node_visitor::visit_option(global.init, |expr| self.visit_expr(expr));
            }
            ast::ItemKind::Err => ()
        } 
    }

    fn visit_field_def(&mut self, field_def: &ast::FieldDef) {
        self.visit_ty_expr(field_def.ty);
        node_visitor::visit_option(field_def.default_init, |default_init| self.visit_expr(default_init));
        field_def.def_id.set(self.resolution.declarations.push(field_def.node_id).into())
            .unwrap();
    }

    fn visit_variant_def(&mut self, variant_def: &ast::VariantDef) {
        node_visitor::visit_option(variant_def.sset, |sset| self.visit_expr(sset));
        variant_def.def_id.set(self.resolution.declarations.push(variant_def.node_id).into())
            .unwrap();
    }

    fn visit_nested_const(&mut self, expr: &ast::NestedConst) {
        self.visit_expr(expr.expr);
        expr.def_id.set(self.resolution.declarations.push(expr.node_id).into())
            .unwrap();
    }
}

#[derive(Default)]
struct Rib {
    symspace: HashMap<Symbol, Local>,
}

struct NameResolutionPass<'r, 'tcx> {
    resolution: &'r mut ResolutionState<'tcx>,
    ribs: Vec<Rib>,
    loop_owners: Vec<NodeId>
}

impl<'r, 'tcx> NameResolutionPass<'r, 'tcx> {
    fn new(resolution: &'r mut ResolutionState<'tcx>) -> Self {
        Self {
            resolution,
            ribs: Default::default(),
            loop_owners: Vec::new()
        }
    }

    fn with_rib<F: FnOnce(&mut Self)>(&mut self, do_work: F) {
        self.ribs.push(Rib::default());
        do_work(self);
        self.ribs.pop();
    }

    fn enter_loop_ctxt<F: FnOnce(&mut Self)>(&mut self, owner: ast::NodeId, do_work: F) {
        self.loop_owners.push(owner);
        do_work(self);
        self.loop_owners.pop();
    }

    fn has_rib(&self) -> bool {
        self.ribs.len() > 0
    }

    fn define(&mut self, name: ast::Ident, site: ast::NodeId) {
        assert!(self.has_rib(), "NameResolutionPass::define() called outside of vaild scope");
        let symbol = name.symbol;
        if let Some(decl) = self.ribs.last().and_then(|rib| rib.symspace.get(&symbol)) {
           Message::error(format!("redeclaration of local {name} here", name = symbol.get()))
                .at(name.span)
                .hint(format!("previous declaration of {name} here", name = symbol.get()), decl.span)
                .push(self.resolution.diagnostics);
            return;
        }
        let decl = Local {
            site,
            span: name.span
        };
        let rib = self.ribs.last_mut().unwrap();
        rib.symspace.insert(symbol, decl);
    }

    fn resolve_local(&self, symbol: Symbol) -> Option<&Local> {
        for rib in self.ribs.iter().rev() {
            if let loc @ Some(_) = rib.symspace.get(&symbol) {
                return loc;
            }
        }
        None
    }

    fn resolve(&self, space: NameSpace, name: &ast::Name, report_error: bool) -> bool {
        if name.resolution().is_some() {
            return true;
        }
        let decl = match space {
            NameSpace::Type => self.resolution.types.get(&name.ident.symbol),
            NameSpace::Function => self.resolution.functions.get(&name.ident.symbol),
            NameSpace::Variable => self.resolution.globals.get(&name.ident.symbol)
        };
        if let Some(decl) = decl {
            name.resolve(Resolution::Def(decl.site, decl.kind));
        } else if let Some(local) = self.resolve_local(name.ident.symbol) {
            name.resolve(Resolution::Local(local.site));
        } else if name.ident.symbol.is_primtive() && space == NameSpace::Type {
            name.resolve(Resolution::Primitive);
        } else {
            if report_error {
                Message::error(format!("could not find {space} {name}", name = name.ident.symbol.get()))
                    .at(name.ident.span)
                    .push(self.resolution.diagnostics);
                name.resolve(Resolution::Err);
            }
            return false;
        };
        true
    }

    fn resolve_priority(&self, pspaces: &[NameSpace], name: &ast::Name) -> bool {
        for space in pspaces {
            if self.resolve(*space, name, false) {
                return true;
            }
        }
        Message::error(format!("could not find {space} {name}", space = pspaces[0], name = name.ident.symbol.get()))
            .at(name.ident.span)
            .push(self.resolution.diagnostics);
        name.resolve(Resolution::Err);
        false
    }
}

impl<'r, 'tcx> Visitor for NameResolutionPass<'r, 'tcx> {
    fn visit_item(&mut self, item: &ast::Item) {
        match &item.kind {
            ast::ItemKind::Function(function) => {
                if function.sig.generics.len() > 0 {
                    let first = function.sig.generics.first().unwrap();
                    let last = function.sig.generics.last().unwrap();
                    Message::fatal("function generics are not supported yet")
                        .at(Span::new(first.span.start, last.span.end))
                        .push(self.resolution.diagnostics);
                }
                self.visit_ty_expr(function.sig.returns);

                let Some(ref body) = function.body else {
                    node_visitor::visit_slice(function.sig.params, |p| self.visit_param(p));
                    return;
                };

                self.with_rib(|this| {
                    node_visitor::visit_slice(function.sig.params, |p| this.visit_param(p));
                    this.visit_expr(body);
                });
            }
            ast::ItemKind::Struct(stc) => {
                if stc.generics.len() > 0 {
                    let first = stc.generics.first().unwrap();
                    let last = stc.generics.last().unwrap();
                    Message::fatal("struct generics are not supported yet")
                        .at(Span::new(first.span.start, last.span.end))
                        .push(self.resolution.diagnostics);
                }
                node_visitor::visit_slice(stc.fields, |field_def| self.visit_field_def(field_def));
            }
            ast::ItemKind::Enum(en) => {
                if let Some(extends) = &en.extends {
                    Message::fatal("enum type extension is not supported yet")
                        .at(Span::new(extends.span.start, extends.span.end))
                        .push(self.resolution.diagnostics);
                }
                node_visitor::visit_slice(en.variants, |variant_def| self.visit_variant_def(variant_def));
            }
            ast::ItemKind::GlobalVar(global_var) => {
                self.visit_ty_expr(global_var.ty);
                node_visitor::visit_option(global_var.init, |expr| self.visit_expr(expr));
            }
            ast::ItemKind::Err => ()
        }
    }

    fn visit_variant_def(&mut self, variant_def: &ast::VariantDef) {
        if let Some(sset) = &variant_def.sset {
            Message::fatal("setting explicit enum tag values is not supported yet")
                .at(Span::new(sset.span.start, sset.span.end))
                .push(self.resolution.diagnostics);
        }
    }

    fn visit_field_def(&mut self, field_def: &ast::FieldDef) {
        if let Some(default_init) = &field_def.default_init {
            Message::fatal("struct default initalizers are not supported yet")
                .at(Span::new(default_init.span.start, field_def.span.end))
                .push(self.resolution.diagnostics);
        }
        self.visit_ty_expr(field_def.ty);
        node_visitor::visit_option(field_def.default_init, |default_init| self.visit_expr(default_init));
    }

    fn visit_stmt(&mut self, stmt: &ast::Stmt) {
        match &stmt.kind {
            ast::StmtKind::Local(local) => {
                node_visitor::visit_option(local.ty, |ret_ty| self.visit_ty_expr(ret_ty));
                node_visitor::visit_option(local.init, |init| self.visit_expr(init));

                self.define(local.ident.clone(), stmt.node_id);
            }
            ast::StmtKind::If(if_stmt) => {
                self.visit_expr(if_stmt.condition);
                self.with_rib(|this| {
                    this.visit_block(&if_stmt.body);
                });
                node_visitor::visit_option(if_stmt.else_branch, |else_body| self.visit_stmt(else_body))
            }
            ast::StmtKind::While(while_loop) => {
                self.visit_expr(while_loop.condition);
                self.with_rib(|this| {
                    this.enter_loop_ctxt(while_loop.body.node_id, |this| this.visit_block(&while_loop.body));
                });
            }
            ast::StmtKind::For(for_loop) => {
                self.define(for_loop.bound_var.clone(), stmt.node_id);
                self.visit_expr(for_loop.iterator);
                self.with_rib(|this| {
                    this.enter_loop_ctxt(for_loop.body.node_id, |this| this.visit_block(&for_loop.body));
                });
            }
            _ => node_visitor::noop_visit_stmt_kind(&stmt.kind, self),
        }
    }

    fn visit_control_flow(&mut self, control_flow: &ast::ControlFlow) {
        let Some(owner) = self.loop_owners.last() else {
            Message::error(format!("`{}` found outside of loop", control_flow.kind))
                .at(control_flow.span)
                .push(self.resolution.diagnostics);

            control_flow.destination.set(Err(OutsideLoopScope));
            return;
        };
        control_flow.destination.set(Ok(*owner));
    }

    fn visit_name(&mut self, name: &ast::Name) {
        self.resolve_priority(&[NameSpace::Variable, NameSpace::Function], name);
    }

    fn visit_expr(&mut self, expr: &ast::Expr) {
        match &expr.kind {
            ast::ExprKind::Name(name) =>
                self.visit_name(name),
            ast::ExprKind::TypeInit(ty_init) => {
                node_visitor::visit_slice(ty_init.initializers, |field| self.visit_type_init(field));
                let Some(ty) = ty_init.ty else {
                    return;
                };
                match &ty.kind {
                    ast::TypeExprKind::Name(name) => {
                        self.resolve(NameSpace::Type, name, true);
                    },
                    ast::TypeExprKind::Array(array) => {
                        self.visit_ty_expr(ty);
                        match array.cap {
                            ast::ArrayCapacity::Discrete(ref expr) =>
                                self.visit_nested_const(expr),
                            ast::ArrayCapacity::Infer | ast::ArrayCapacity::Dynamic => ()
                        }
                    }
                    ast::TypeExprKind::Slice(ty) =>
                        self.visit_ty_expr(ty),
                    ast::TypeExprKind::Generic(..) => {
                        Message::fatal("generic types are not supported yet")
                            .at(ty.span)
                            .push(self.resolution.diagnostics);
                    }
                    ast::TypeExprKind::Ref(..) =>
                        panic!("invalid state after parsing type init"),
                    ast::TypeExprKind::Err => ()
                }
            }
            ast::ExprKind::FunctionCall(call) if matches!(&call.callable.kind, ast::ExprKind::Name(..)) => {
                let ast::ExprKind::Name(name) = &call.callable.kind else {
                    unreachable!();
                };
                if call.generic_args.len() > 0 {
                    Message::fatal("generic function calls are not supported yet")
                        .at(expr.span)
                        .push(self.resolution.diagnostics);
                    return;
                }
                node_visitor::visit_slice(call.args, |arg| self.visit_argument(arg));
                self.resolve_priority(&[NameSpace::Function, NameSpace::Variable], name);
            }
            ast::ExprKind::Block(body) => {
                self.with_rib(|this| {
                    this.visit_block(body);
                });
            }
            ast::ExprKind::Field(field) =>
                self.visit_expr(field.expr),
            _ => node_visitor::noop_visit_expr_kind(&expr.kind, self)
        }
    }

    fn visit_param(&mut self, param: &ast::Param) {
        self.visit_ty_expr(&param.ty);

        if !self.has_rib() {
            return;
        }

        self.define(param.ident.clone(), param.node_id);
    }

    fn visit_ty_expr(&mut self, ty: &ast::TypeExpr) {
        match &ty.kind {
            ast::TypeExprKind::Ref(ty) => self.visit_ty_expr(ty),
            ast::TypeExprKind::Name(name) => {
                self.resolve(NameSpace::Type, name, true);
            },
            ast::TypeExprKind::Generic(..) => {
                Message::fatal("generic types are not supported yet")
                    .at(ty.span)
                    .push(self.resolution.diagnostics);
            }
            ast::TypeExprKind::Array(array) => {
                self.visit_ty_expr(array.ty);
                match array.cap {
                    ast::ArrayCapacity::Discrete(ref expr) =>
                        self.visit_nested_const(expr),
                    ast::ArrayCapacity::Infer | ast::ArrayCapacity::Dynamic => ()
                }
            }
            k @ _ => node_visitor::noop_visit_ty_expr_kind(k, self)
        }
    }
}

pub fn run_resolve<'tcx>(
    tcx: TyCtxt<'tcx>, mut tree: ast::SourceFile
) -> ResolutionResults {
    let mut resolution = ResolutionState::new(tcx.diagnostics());

    let mut rpass = TypeResolutionPass::new(&mut resolution);
    rpass.resolve(&mut tree);

    let mut rpass = NameResolutionPass::new(&mut resolution);
    rpass.visit(&mut tree);

    println!("{tree:#?}");

    resolution.results()
}

