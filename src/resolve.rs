
use std::{collections::HashMap, ops::Range};

use crate::{ast::{self, NameInNamespace, DeclarationKind}, node_visitor::{MutVisitor, self}, diagnostics::{Diagnostics, self}, symbol::Symbol};

/// AST (&tree) 
///     |          |
/// Types & Fn's   |                                |
///          assoc vars, fields, args with types    |
///                                                 |
///                                           Name <-> declaration site (NodeId)

enum Symbolspace {
    Type, Function, Global 
}

impl std::fmt::Display for Symbolspace {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Symbolspace as Sym;
        match self {
            Sym::Type => write!(f, "type"),
            Sym::Function => write!(f, "function"),
            Sym::Global => write!(f, "global"),
        }
    }
}

struct Declaration {
    site: ast::NodeId,
    span: Range<usize>,
}

struct ResolutionState {
    diagnostics: Diagnostics,
    types: HashMap<Symbol, Declaration>,
    functions: HashMap<Symbol, Declaration>,
    globals: HashMap<Symbol, Declaration>,
}

impl ResolutionState {
    fn new(diagnostics: Diagnostics) -> ResolutionState {
        ResolutionState {
            diagnostics,
            types: Default::default(),
            functions: Default::default(),
            globals: Default::default(),
        }
    }

    fn define(&mut self, space_kind: Symbolspace, name: ast::Ident, site: ast::NodeId) {
        let space = match space_kind {
            Symbolspace::Type => &mut self.types,
            Symbolspace::Function => &mut self.functions,
            Symbolspace::Global => &mut self.globals,
        };
        let declaration = Declaration {
            site, span: name.span.clone()
        };
        if let Some(prev) = space.insert(name.symbol, declaration) {
            self.diagnostics
                .error(format!("redeclaration of {space_kind} {name:?}", name = name.symbol.get()))
                .with_span(name.span);
            self.diagnostics
                .note(format!("previous declaration of {name:?} here", name = name.symbol.get()))
                .with_pos(prev.span.start);
        }
    }
}

struct TypeResolutionPass<'r> {
    resolution: &'r mut ResolutionState,
    current_node_id: u32
}

impl<'r> TypeResolutionPass<'r> {
    fn new(resolution: &'r mut ResolutionState) -> Self {
        Self { resolution, current_node_id: 0 }
    }

    fn resolve(&mut self, tree: &mut ast::TopLevel) {
        self.current_node_id = tree.node_id.0;
        self.visit(tree);
        tree.node_id.0 = self.current_node_id;
    }

    fn make_node_id(&mut self) -> ast::NodeId {
        let new_node_id = self.current_node_id + 1;
        ast::NodeId(std::mem::replace(&mut self.current_node_id, new_node_id))
    }
}

impl<'r> MutVisitor for TypeResolutionPass<'r> {
    fn visit_item(&mut self, item: &mut ast::Item) {
        match &mut item.kind {
            ast::ItemKind::Record(rec) => {
                self.resolution.define(Symbolspace::Type, item.ident.clone(), item.node_id);
                node_visitor::visit_vec(&mut rec.fields, |field_def| self.visit_field_def(field_def));
                node_visitor::visit_vec(&mut rec.generics, |generic| self.visit_generic_param(generic));
            },
            ast::ItemKind::Proc(proc) => {
                self.resolution.define(Symbolspace::Function, item.ident.clone(), item.node_id);
                node_visitor::visit_proc(proc, self);
            },
            _ => node_visitor::noop_visit_item_kind(&mut item.kind, self),
        } 
    }

    fn visit_expr(&mut self, expr: &mut ast::Expr) { 
        match &mut expr.kind {
            ast::ExprKind::Path(..) => {
                let kind = core::mem::replace(&mut expr.kind, ast::ExprKind::Err);
                let (mut path, ident) = match kind {
                    ast::ExprKind::Path(ast::QPath::Unresolved(path, ident)) => (path, ident),
                    _ => panic!("invalid state in path replace resolution"),
                };
                path.segments.push(ident);
                let base = path.segments.remove(0);
                let mut rexpr = ast::Expr {
                    span: base.span.clone(),
                    kind: ast::ExprKind::Name(ast::QName::Unresolved(base)),
                    node_id: self.make_node_id() 
                };
                for ident in path.segments {
                    rexpr = ast::Expr {
                        span: (rexpr.span.start..ident.span.end),
                        kind: ast::ExprKind::Attribute(Box::new(rexpr), ident),
                        node_id: self.make_node_id()
                    };
                }
                expr.kind = rexpr.kind;
            },
            _ => node_visitor::noop_visit_expr_kind(&mut expr.kind, self),
        }
    }
}

#[derive(Default)]
struct Rib {
    symspace: HashMap<Symbol, Declaration>,
}

struct NameResolutionPass<'r> {
    resolution: &'r mut ResolutionState,
    ribs: Vec<Rib>
}

impl<'r> NameResolutionPass<'r> {
    fn new(resolution: &'r mut ResolutionState) -> Self {
        Self {
            resolution,
            ribs: Default::default()
        }
    }

    fn with_rib<F: FnOnce(&mut Self)>(&mut self, do_work: F) {
        self.ribs.push(Rib::default());
        do_work(self);
        self.ribs.pop();
    }

    fn has_rib(&self) -> bool {
        self.ribs.len() > 0
    }

    fn define(&mut self, name: ast::Ident, site: ast::NodeId) {
        assert!(self.has_rib(), "NameResolutionPass::define() called outside of vaild scope");
        let symbol = name.symbol;
        for rib in &self.ribs {
            if let Some(decl) = rib.symspace.get(&symbol)  {
                self.resolution.diagnostics
                    .error(format!("redeclaration of var {name} here", name = symbol.get()))
                    .with_span(name.span.clone());
                self.resolution.diagnostics
                    .note(format!("previous declaration of {name} here", name = symbol.get()))
                    .with_span(decl.span.clone());
                return;
            };
        }
        let decl = Declaration {
            site,
            span: name.span.clone()
        };
        let rib = self.ribs.last_mut().unwrap();
        rib.symspace.insert(symbol, decl);
    }
}

impl<'r> MutVisitor for NameResolutionPass<'r> {
    fn visit_item(&mut self, item: &mut ast::Item) {
        match &mut item.kind {
            ast::ItemKind::Proc(proc) => {
                if proc.generics.len() > 0 {
                    let first = proc.generics.first().unwrap();
                    let last = proc.generics.last().unwrap();
                    self.resolution.diagnostics
                        .error("procedure generics are not supported yet")
                        .with_span(first.span.start..last.span.end);
                }
                node_visitor::visit_option(&mut proc.returns, |ty| self.visit_ty_expr(ty));

                let Some(ref mut body) = proc.body else {
                    node_visitor::visit_vec(&mut proc.params, |p| self.visit_param(p));
                    return;
                };

                self.with_rib(|this| {
                    node_visitor::visit_vec(&mut proc.params, |p| this.visit_param(p));
                    node_visitor::visit_vec(body, |stmt| this.visit_stmt(stmt));
                });
            }
            ast::ItemKind::Record(rec) => {
                if rec.generics.len() > 0 {
                    let first = rec.generics.first().unwrap();
                    let last = rec.generics.last().unwrap();
                    self.resolution.diagnostics
                        .error("record generics are not supported yet")
                        .with_span(first.span.start..last.span.end);
                }
                node_visitor::visit_vec(&mut rec.fields, |field_def| self.visit_field_def(field_def));
            }
            ast::ItemKind::Constant(ty, expr) => {
                self.visit_ty_expr(ty);
                self.visit_expr(expr);
            }
            ast::ItemKind::StaticVar(ty, expr) => {
                node_visitor::visit_option(ty, |ty| self.visit_ty_expr(ty));
                node_visitor::visit_option(expr, |expr| self.visit_expr(expr));
            }
            ast::ItemKind::Err => ()
        }
    }

    fn visit_param(&mut self, param: &mut ast::Param) {
        let ident = match &param.pat.kind {
            ast::PatternKind::Ident(ident) => ident.clone(),
            ast::PatternKind::Tuple(..) => {
                self.resolution.diagnostics
                    .error(format!("tuple arguments are not supported yet"))
                    .with_span(param.pat.span.clone());
                return;
            }
            ast::PatternKind::Literal(..) | ast::PatternKind::Path(..) => {
                self.resolution.diagnostics
                    .error(format!("unsensible pattern found in function argument"))
                    .with_span(param.pat.span.clone());
                param.pat.kind = ast::PatternKind::Ident(ast::Ident::from_str("_"));
                return;
            }
        };
        self.visit_ty_expr(&mut param.ty);

        if !self.has_rib() {
            return;
        }

        self.define(ident, param.node_id);
    }

    fn visit_ty_expr(&mut self, ty: &mut ast::TypeExpr) {
        match &mut ty.kind {
            ast::TypeExprKind::Ref(ty) => self.visit_ty_expr(ty),
            ast::TypeExprKind::Name(name) => match name {
                NameInNamespace::Name(name) => {
                    let ident = match name {
                        ast::QName::Unresolved(ident) => ident.clone(),
                        ast::QName::Resolved { .. } => return,
                    };
                    if let Some(decl) = self.resolution.types.get(&ident.symbol) {
                        *name = ast::QName::Resolved {
                            ident,
                            node_id: decl.site,
                            res_kind: DeclarationKind::Type
                        };
                    } else if ident.symbol.is_primtive() {
                        *name = ast::QName::Resolved {
                            ident,
                            node_id: ast::NODE_ID_UNDEF,
                            res_kind: DeclarationKind::Primitive
                        };
                    } else { 
                        self.resolution.diagnostics
                            .error(format!("could not find type {name}", name = ident.symbol.get()))
                            .with_span(ident.span.clone());
                        *name = ast::QName::Resolved {
                            ident,
                            node_id: ast::NODE_ID_UNDEF,
                            res_kind: DeclarationKind::Err
                        };
                    }
                },
                NameInNamespace::Path(path) => self.visit_path(path),
            },
            ast::TypeExprKind::Generic(..) => {
                self.resolution.diagnostics
                    .error("generic types are not supported yet")
                    .with_span(ty.span.clone());
            }
            ast::TypeExprKind::Function { .. } => {
                self.resolution.diagnostics
                    .error("procedure types are not supported yet")
                    .with_span(ty.span.clone());
            }
        }
    }

    fn visit_path(&mut self, path: &mut ast::QPath) {
        let (path, ident) = match path {
            ast::QPath::Unresolved(path, ident) => (path, ident), 
            ast::QPath::Resolved => panic!("invalid state when emitting path error"),
        };
        self.resolution.diagnostics
            .error("there is no namespace support yet")
            .with_span(path.span.start..ident.span.end);
    }
}

pub fn run_resolve(tree: &mut ast::TopLevel) {
    let mut resolution = ResolutionState::new(tree.diagnostics);

    let mut rpass = TypeResolutionPass::new(&mut resolution);
    rpass.resolve(tree);

    let mut rpass = NameResolutionPass::new(&mut resolution);
    rpass.visit(tree);
}

