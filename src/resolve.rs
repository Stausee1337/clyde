
use std::collections::HashMap;

use crate::{ast::{self, Resolution, DefinitionKind, NodeId}, node_visitor::{MutVisitor, self}, diagnostics::DiagnosticsCtxt, symbol::Symbol, context::TyCtxt, lexer::Span};

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
            self.diagnostics
                .error(format!("redeclaration of {space} {name:?}", name = name.symbol.get()))
                .with_span(name.span);
            self.diagnostics
                .note(format!("previous declaration of {name:?} here", name = name.symbol.get()))
                .with_pos(prev.span.start);
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

impl<'r, 'tcx> MutVisitor for TypeResolutionPass<'r, 'tcx> {
    fn visit_item(&mut self, item: &mut ast::Item) {
        match &mut item.kind {
            ast::ItemKind::Struct(stc) => {
                self.resolution.define(DefinitionKind::Struct, item.ident.clone(), item.node_id);
                node_visitor::visit_vec(&mut stc.fields, |field_def| self.visit_field_def(field_def));
                node_visitor::visit_vec(&mut stc.generics, |generic| self.visit_generic_param(generic));
            }, 
            ast::ItemKind::Enum(en) => {
                self.resolution.define(DefinitionKind::Enum, item.ident.clone(), item.node_id);
                node_visitor::visit_vec(&mut en.variants, |variant_def| self.visit_variant_def(variant_def));
            },
            ast::ItemKind::Function(function) => {
                self.resolution.define(DefinitionKind::Function, item.ident.clone(), item.node_id);
                node_visitor::visit_fn(function, self);
            },
            ast::ItemKind::GlobalVar(ty, expr, is_const) => {
                self.resolution.define(
                    if *is_const {DefinitionKind::Global} else {DefinitionKind::Const},
                    item.ident.clone(), item.node_id);
                self.visit_ty_expr(ty);
                node_visitor::visit_option(expr, |expr| self.visit_expr(expr));
            }
            ast::ItemKind::Err => ()
        } 
    }

    fn visit_field_def(&mut self, field_def: &mut ast::FieldDef) {
        self.visit_ty_expr(&mut field_def.ty);
        node_visitor::visit_option(&mut field_def.default_init, |default_init| self.visit_expr(default_init));
        field_def.def_id = self.resolution.declarations.push(field_def.node_id).into();
    }

    fn visit_variant_def(&mut self, variant_def: &mut ast::VariantDef) {
        node_visitor::visit_option(&mut variant_def.sset, |sset| self.visit_expr(sset));
        variant_def.def_id = self.resolution.declarations.push(variant_def.node_id).into();
    }

    fn visit_nested_const(&mut self, expr: &mut ast::NestedConst) {
        self.visit_expr(&mut expr.expr);
        expr.def_id = self.resolution.declarations.push(expr.node_id).into();
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
            self.resolution.diagnostics
                .error(format!("redeclaration of local {name} here", name = symbol.get()))
                .with_span(name.span);
            self.resolution.diagnostics
                .note(format!("previous declaration of {name} here", name = symbol.get()))
                .with_span(decl.span);
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

    fn resolve(&self, space: NameSpace, name: &mut ast::QName, report_error: bool) -> bool {
        let ident = match name {
            ast::QName::Unresolved(ident) => ident.clone(),
            ast::QName::Resolved { .. } => return true,
        };
        let decl = match space {
            NameSpace::Type => self.resolution.types.get(&ident.symbol),
            NameSpace::Function => self.resolution.functions.get(&ident.symbol),
            NameSpace::Variable => self.resolution.globals.get(&ident.symbol)
        };
        if let Some(decl) = decl {
            *name = ast::QName::Resolved {
                ident,
                res_kind: Resolution::Def(decl.site, decl.kind)
            };
        } else if let Some(local) = self.resolve_local(ident.symbol) {
            *name = ast::QName::Resolved {
                ident,
                res_kind: Resolution::Local(local.site)
            };
        } else if ident.symbol.is_primtive() && space == NameSpace::Type {
            *name = ast::QName::Resolved {
                ident,
                res_kind: Resolution::Primitive
            };
        } else {
            if report_error {
                self.resolution.diagnostics
                    .error(format!("could not find {space} {name}", name = ident.symbol.get()))
                    .with_span(ident.span);
                *name = ast::QName::Resolved {
                    ident,
                    res_kind: Resolution::Err
                };
            }
            return false;
        };
        true
    }

    fn resolve_priority(&self, pspaces: &[NameSpace], name: &mut ast::QName) -> bool {
        for space in pspaces {
            if self.resolve(*space, name, false) {
                return true;
            }
        }
        let ident = match name {
            ast::QName::Unresolved(ident) => ident.clone(),
            ast::QName::Resolved { .. } => panic!(),
        };
        self.resolution.diagnostics
            .error(format!("could not find {space} {name}", space = pspaces[0], name = ident.symbol.get()))
            .with_span(ident.span);
        *name = ast::QName::Resolved {
            ident,
            res_kind: Resolution::Err
        };
        false
    }
}

impl<'r, 'tcx> MutVisitor for NameResolutionPass<'r, 'tcx> {
    fn visit_item(&mut self, item: &mut ast::Item) {
        match &mut item.kind {
            ast::ItemKind::Function(function) => {
                if function.sig.generics.len() > 0 {
                    let first = function.sig.generics.first().unwrap();
                    let last = function.sig.generics.last().unwrap();
                    self.resolution.diagnostics
                        .fatal("function generics are not supported yet")
                        .with_span(Span::new(first.span.start, last.span.end));
                }
                self.visit_ty_expr(&mut function.sig.returns);

                let Some(ref mut body) = function.body else {
                    node_visitor::visit_vec(&mut function.sig.params, |p| self.visit_param(p));
                    return;
                };

                self.with_rib(|this| {
                    node_visitor::visit_vec(&mut function.sig.params, |p| this.visit_param(p));
                    this.visit_expr(body);
                });
            }
            ast::ItemKind::Struct(stc) => {
                if stc.generics.len() > 0 {
                    let first = stc.generics.first().unwrap();
                    let last = stc.generics.last().unwrap();
                    self.resolution.diagnostics
                        .fatal("struct generics are not supported yet")
                        .with_span(Span::new(first.span.start, last.span.end));
                }
                node_visitor::visit_vec(&mut stc.fields, |field_def| self.visit_field_def(field_def));
            }
            ast::ItemKind::Enum(en) => {
                if let Some(extends) = &en.extends {
                    self.resolution.diagnostics
                        .fatal("enum type extension is not supported yet")
                        .with_span(Span::new(extends.span.start, extends.span.end));
                }
                node_visitor::visit_vec(&mut en.variants, |variant_def| self.visit_variant_def(variant_def));
            }
            ast::ItemKind::GlobalVar(ty, expr, _) => {
                self.visit_ty_expr(ty);
                node_visitor::visit_option(expr, |expr| self.visit_expr(expr));
            }
            ast::ItemKind::Err => ()
        }
    }

    fn visit_variant_def(&mut self, variant_def: &mut ast::VariantDef) {
        if let Some(sset) = &variant_def.sset {
            self.resolution.diagnostics
                .fatal("setting explicit enum tag values is not supported yet")
                .with_span(Span::new(sset.span.start, sset.span.end));
        }
    }

    fn visit_field_def(&mut self, field_def: &mut ast::FieldDef) {
        if let Some(default_init) = &field_def.default_init {
            self.resolution.diagnostics
                .fatal("struct default initalizers are not supported yet")
                .with_span(Span::new(default_init.span.start, field_def.span.end));
        }
        self.visit_ty_expr(&mut field_def.ty);
        node_visitor::visit_option(&mut field_def.default_init, |default_init| self.visit_expr(default_init));
    }

    fn visit_stmt(&mut self, stmt: &mut ast::Stmt) {
        match &mut stmt.kind {
            ast::StmtKind::Local(ident, ret_ty, init) => {
                node_visitor::visit_option(ret_ty, |ret_ty| self.visit_ty_expr(ret_ty));
                node_visitor::visit_option(init, |init| self.visit_expr(init));

                self.define(ident.clone(), stmt.node_id);
            }
            ast::StmtKind::If(cond, body, else_body) => {
                self.visit_expr(cond);
                self.with_rib(|this| {
                    this.visit_block(body);
                });
                node_visitor::visit_option(else_body, |else_body| self.visit_stmt(else_body))
            }
            ast::StmtKind::While(cond, body) => {
                self.visit_expr(cond);
                self.with_rib(|this| {
                    this.enter_loop_ctxt(body.node_id, |this| this.visit_block(body));
                });
            }
            ast::StmtKind::For(ident, iter, body) => {
                self.define(ident.clone(), stmt.node_id);
                self.visit_expr(iter);
                self.with_rib(|this| {
                    this.enter_loop_ctxt(body.node_id, |this| this.visit_block(body));
                });
            }
            _ => node_visitor::noop_visit_stmt_kind(&mut stmt.kind, self),
        }
    }

    fn visit_control_flow(&mut self, control_flow: &mut ast::ControlFlow) {
        let Some(owner) = self.loop_owners.last() else {
            self.resolution.diagnostics.error(format!("`{}` found outside of loop", control_flow.kind))
                .with_span(control_flow.span);
            return;
        };
        control_flow.destination = Ok(*owner);
    }

    fn visit_name(&mut self, name: &mut ast::QName) {
        self.resolve_priority(&[NameSpace::Variable, NameSpace::Function], name);
    }

    fn visit_expr(&mut self, expr: &mut ast::Expr) {
        match &mut expr.kind {
            ast::ExprKind::Name(name) =>
                self.visit_name(name),
            ast::ExprKind::TypeInit(ty, fields) => {
                node_visitor::visit_vec(fields, |field| self.visit_type_init(field));
                let Some(ty) = ty else {
                    return;
                };
                match &mut ty.kind {
                    ast::TypeExprKind::Name(name) => {
                        self.resolve(NameSpace::Type, name, true);
                    },
                    ast::TypeExprKind::Array(ty, cap) => {
                        self.visit_ty_expr(ty);
                        match cap {
                            ast::ArrayCapacity::Discrete(expr) =>
                                self.visit_nested_const(expr),
                            ast::ArrayCapacity::Infer | ast::ArrayCapacity::Dynamic => ()
                        }
                    }
                    ast::TypeExprKind::Slice(ty) =>
                        self.visit_ty_expr(ty),
                    ast::TypeExprKind::Generic(..) => {
                        self.resolution.diagnostics
                            .fatal("generic types are not supported yet")
                            .with_span(ty.span);
                    }
                    ast::TypeExprKind::Ref(..) | ast::TypeExprKind::Tuple(..) =>
                        panic!("invalid state after parsing type init"),
                }
            }
            ast::ExprKind::FunctionCall(base, args, generic_args) if matches!(&base.kind, ast::ExprKind::Name(..)) => {
                let ast::ExprKind::Name(name) = &mut base.kind else {
                    panic!();
                };
                if generic_args.len() > 0 {
                    self.resolution.diagnostics
                        .fatal("generic function calls are not supported yet")
                        .with_span(expr.span);
                    return;
                }
                node_visitor::visit_vec(args, |arg| self.visit_argument(arg));
                self.resolve_priority(&[NameSpace::Function, NameSpace::Variable], name);
            }
            ast::ExprKind::Block(body) => {
                self.with_rib(|this| {
                    this.visit_block(body);
                });
            }
            ast::ExprKind::Field(base, ident) => match (base.as_mut(), ident) {
                (ast::Expr { kind: ast::ExprKind::Name(name), node_id: spare_id, .. }, ast::FieldIdent::Named(variant)) => {
                    let res = if name.ident().symbol.get().chars().nth(0).unwrap().is_uppercase() {
                        // types (enums) get higher priority if the beginning char of the name is
                        // uppercase
                        self.resolve_priority(&[NameSpace::Type, NameSpace::Variable, NameSpace::Function], name)
                    } else {
                        self.resolve_priority(&[NameSpace::Variable, NameSpace::Function, NameSpace::Type], name)
                    };
                    if let ast::QName::Resolved { res_kind: ast::Resolution::Def(_, ast::DefinitionKind::Enum), .. }
                        = name {
                        assert!(res);
                        let span = expr.span;
                        let node_id = expr.node_id;

                        let enm = {
                            let span = name.ident().span;
                            ast::TypeExpr {
                                span,
                                kind: ast::TypeExprKind::Name(name.clone()),
                                node_id: *spare_id
                            }
                        };

                        *expr = ast::Expr {
                            kind: ast::ExprKind::EnumVariant(Box::new(enm), variant.clone()),
                            span,
                            node_id
                        };
                    }
                }
                _ => self.visit_expr(base)
            },
            _ => node_visitor::noop_visit_expr_kind(&mut expr.kind, self)
        }
    }

    fn visit_param(&mut self, param: &mut ast::Param) {
        self.visit_ty_expr(&mut param.ty);

        if !self.has_rib() {
            return;
        }

        self.define(param.ident.clone(), param.node_id);
    }

    fn visit_ty_expr(&mut self, ty: &mut ast::TypeExpr) {
        match &mut ty.kind {
            ast::TypeExprKind::Ref(ty) => self.visit_ty_expr(ty),
            ast::TypeExprKind::Name(name) => {
                self.resolve(NameSpace::Type, name, true);
            },
            ast::TypeExprKind::Generic(..) => {
                self.resolution.diagnostics
                    .fatal("generic types are not supported yet")
                    .with_span(ty.span);
            }
            ast::TypeExprKind::Array(base, cap) => {
                self.visit_ty_expr(base);
                match cap {
                    ast::ArrayCapacity::Discrete(expr) =>
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

