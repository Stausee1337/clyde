
use std::{collections::HashMap, ops::Range};

use crate::{ast::{self, DeclarationKind}, node_visitor::{MutVisitor, self, noop_visit_stmt_kind}, diagnostics::Diagnostics, symbol::Symbol};

/// AST (&tree) 
///     |          |
/// Types & Fn's   |                                |
///          assoc vars, fields, args with types    |
///                                                 |
///                                           Name <-> declaration site (NodeId)


#[derive(Clone, Copy, PartialEq, Eq)]
enum Symbolspace {
    Type, Function, Variable 
}

impl std::fmt::Display for Symbolspace {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Symbolspace as Sym;
        match self {
            Sym::Type => write!(f, "type"),
            Sym::Function => write!(f, "function"),
            Sym::Variable => write!(f, "var"),
        }
    }
}

#[derive(Clone)]
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
            Symbolspace::Variable => &mut self.globals,
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
            ast::ItemKind::Constant(ty, expr) => {
                self.resolution.define(Symbolspace::Variable, item.ident.clone(), item.node_id);
                self.visit_ty_expr(ty);
                self.visit_expr(expr);
            }
            ast::ItemKind::StaticVar(ty, expr) => {
                self.resolution.define(Symbolspace::Variable, item.ident.clone(), item.node_id);
                node_visitor::visit_option(ty, |ty| self.visit_ty_expr(ty));
                node_visitor::visit_option(expr, |expr| self.visit_expr(expr));
            }
            ast::ItemKind::Err => ()
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
        if let Some(decl) = self.resolve_local(symbol) {
            self.resolution.diagnostics
                .error(format!("redeclaration of var {name} here", name = symbol.get()))
                .with_span(name.span.clone());
            self.resolution.diagnostics
                .note(format!("previous declaration of {name} here", name = symbol.get()))
                .with_span(decl.span.clone());
            return;
        }
        let decl = Declaration {
            site,
            span: name.span.clone()
        };
        let rib = self.ribs.last_mut().unwrap();
        rib.symspace.insert(symbol, decl);
    }

    fn resolve_local(&self, symbol: Symbol) -> Option<&Declaration> {
        for rib in self.ribs.iter().rev() {
            if let decl @ Some(_) = rib.symspace.get(&symbol) {
                return decl;
            }
        }
        None
    }

    fn resolve(&self, space: Symbolspace, name: &mut ast::QName, report_error: bool) -> bool {
        let ident = match name {
            ast::QName::Unresolved(ident) => ident.clone(),
            ast::QName::Resolved { .. } => return true,
        };
        let mut is_local = true;
        let decl = match space {
            Symbolspace::Type => self.resolution.types.get(&ident.symbol),
            Symbolspace::Function => self.resolution.functions.get(&ident.symbol),
            Symbolspace::Variable => {
                self.resolve_local(ident.symbol)
                    .or_else(|| {
                        is_local = false;
                        self.resolution.globals.get(&ident.symbol)
                    })
            },
        };
        if let Some(decl) = decl {
            let res_kind = match space {
                Symbolspace::Type => DeclarationKind::Type,
                Symbolspace::Function => DeclarationKind::Function,
                Symbolspace::Variable => if is_local { DeclarationKind::Local } else { DeclarationKind::Global }
            };
            *name = ast::QName::Resolved {
                ident,
                node_id: decl.site,
                res_kind
            };
        } else if ident.symbol.is_primtive() && space == Symbolspace::Type {
            *name = ast::QName::Resolved {
                ident,
                node_id: ast::NODE_ID_UNDEF,
                res_kind: DeclarationKind::Primitive
            };
        } else {
            if report_error {
                self.resolution.diagnostics
                    .error(format!("could not find {space} {name}", name = ident.symbol.get()))
                    .with_span(ident.span.clone());
                *name = ast::QName::Resolved {
                    ident,
                    node_id: ast::NODE_ID_UNDEF,
                    res_kind: DeclarationKind::Err
                };
            }
            return false;
        };
        true
    }

    fn resolve_priority(&self, pspaces: &[Symbolspace], name: &mut ast::QName) -> bool {
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
            .with_span(ident.span.clone());
        false
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
                        .fatal("procedure generics are not supported yet")
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
                        .fatal("record generics are not supported yet")
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

    fn visit_stmt(&mut self, stmt: &mut ast::Stmt) {
        match &mut stmt.kind {
            ast::StmtKind::Local(pat, ret_ty, init) => {
                let ident = match &pat.kind {
                    ast::PatternKind::Ident(ident) => ident.clone(),
                    ast::PatternKind::Tuple(..) => {
                        self.resolution.diagnostics
                            .fatal(format!("tuple pattern in function parameters are not supported yet"))
                            .with_span(pat.span.clone());
                        return;
                    }
                    ast::PatternKind::Literal(..) | ast::PatternKind::Path(..) => {
                        self.resolution.diagnostics
                            .error(format!("unsensible pattern found in var declaration"))
                            .with_span(pat.span.clone());
                        return;
                    }
                };

                node_visitor::visit_option(ret_ty, |ret_ty| self.visit_ty_expr(ret_ty));
                node_visitor::visit_option(init, |init| self.visit_expr(init));

                self.define(ident, stmt.node_id);
            }
            ast::StmtKind::If(cond, body, else_body) => {
                self.visit_expr(cond);
                self.with_rib(|this| {
                    node_visitor::visit_vec(body, |stmt| this.visit_stmt(stmt));
                });
                node_visitor::visit_option(else_body, |else_body| self.visit_stmt(else_body))
            }
            ast::StmtKind::While(cond, body) => {
                self.visit_expr(cond);
                self.with_rib(|this| {
                    node_visitor::visit_vec(body, |stmt| this.visit_stmt(stmt));
                });
            }
            ast::StmtKind::For(..) => {
                self.resolution.diagnostics
                    .fatal("for loops are not supported yet")
                    .with_span(stmt.span.clone());
                self.resolution.diagnostics
                    .note("consider using while loops for now")
                    .with_pos(stmt.span.start);
                stmt.kind = ast::StmtKind::Err;
            }
            ast::StmtKind::Item(..) => {
                self.resolution.diagnostics
                    .fatal("inner items are not supported yet")
                    .with_span(stmt.span.clone());
            }
            _ => noop_visit_stmt_kind(&mut stmt.kind, self),
        }
    }

    fn visit_expr(&mut self, expr: &mut ast::Expr) {
        match &mut expr.kind {
            ast::ExprKind::Name(name) => {
                self.resolve_priority(&[Symbolspace::Variable, Symbolspace::Function, Symbolspace::Type], name);
            }
            ast::ExprKind::RecordInit(name, fields) => {
                node_visitor::visit_vec(fields, |field| self.visit_field_init(field));
                self.resolve(Symbolspace::Type, name, true);
            }
            ast::ExprKind::FunctionCall(base, args) if matches!(&base.kind, ast::ExprKind::Name(..)) => {
                let ast::ExprKind::Name(name) = &mut base.kind else {
                    panic!();
                };
                node_visitor::visit_vec(args, |arg| self.visit_argument(arg));
                self.resolve_priority(&[Symbolspace::Function, Symbolspace::Variable], name);
            }
            ast::ExprKind::PatternMatch(..) => {
                self.resolution.diagnostics
                    .fatal("pattern matching is not supported yet")
                    .with_span(expr.span.clone());
            }
            _ => node_visitor::noop_visit_expr_kind(&mut expr.kind, self)
        }
    }

    fn visit_param(&mut self, param: &mut ast::Param) {
        let ident = match &param.pat.kind {
            ast::PatternKind::Ident(ident) => ident.clone(),
            ast::PatternKind::Tuple(..) => {
                self.resolution.diagnostics
                    .fatal(format!("tuple pattern in function parameters are not supported yet"))
                    .with_span(param.pat.span.clone());
                return;
            }
            ast::PatternKind::Literal(..) | ast::PatternKind::Path(..) => {
                self.resolution.diagnostics
                    .error(format!("unsensible pattern found in function parameter"))
                    .with_span(param.pat.span.clone());
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
            ast::TypeExprKind::Name(name) => {
                self.resolve(Symbolspace::Type, name, true);
            },
            ast::TypeExprKind::Generic(..) => {
                self.resolution.diagnostics
                    .fatal("generic types are not supported yet")
                    .with_span(ty.span.clone());
            }
            ast::TypeExprKind::Function { .. } => {
                self.resolution.diagnostics
                    .fatal("procedure types are not supported yet")
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

