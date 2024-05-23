
use std::{collections::HashMap, ops::Range};

use crate::{ast::{self, Resolution, DefinitonKind}, node_visitor::{MutVisitor, self, noop_visit_stmt_kind}, diagnostics::Diagnostics, symbol::Symbol};

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
            Sym::Variable => write!(f, "var"),
        }
    }
}

impl From<DefinitonKind> for NameSpace {
    fn from(value: DefinitonKind) -> Self {
        use DefinitonKind as D;
        match value {
            D::Struct => NameSpace::Type,
            D::Function => NameSpace::Function,
            D::Global | D::Const => NameSpace::Variable,
        }
    }
}

#[derive(Clone)]
struct Declaration {
    site: ast::DefId,
    kind: DefinitonKind,
    span: Range<usize>,
}

#[derive(Clone)]
struct Local {
    site: ast::NodeId,
    span: Range<usize>,
}

struct ResolutionState {
    diagnostics: Diagnostics,
    types: HashMap<Symbol, Declaration>,
    functions: HashMap<Symbol, Declaration>,
    globals: HashMap<Symbol, Declaration>,
    declarations: index_vec::IndexVec<ast::DefIndex, ast::NodeId>
}

impl ResolutionState {
    fn new(diagnostics: Diagnostics) -> ResolutionState {
        ResolutionState {
            diagnostics,
            types: Default::default(),
            functions: Default::default(),
            globals: Default::default(),
            declarations: Default::default()
        }
    }

    fn define(&mut self, kind: DefinitonKind, name: ast::Ident, site: ast::NodeId) {
        let space = match kind {
            DefinitonKind::Struct => &mut self.types,
            DefinitonKind::Function => &mut self.functions,
            DefinitonKind::Global | DefinitonKind::Const => &mut self.globals,
        };
        let declaration = Declaration {
            site: self.declarations.push(site).into(), kind, span: name.span.clone()
        };
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
}

struct TypeResolutionPass<'r> {
    resolution: &'r mut ResolutionState,
}

impl<'r> TypeResolutionPass<'r> {
    fn new(resolution: &'r mut ResolutionState) -> Self {
        Self { resolution }
    }

    fn resolve(&mut self, tree: &mut ast::TopLevel) {
        self.visit(tree);
    }
}

impl<'r> MutVisitor for TypeResolutionPass<'r> {
    fn visit_item(&mut self, item: &mut ast::Item) {
        match &mut item.kind {
            ast::ItemKind::Struct(stc) => {
                self.resolution.define(DefinitonKind::Struct, item.ident.clone(), item.node_id);
                node_visitor::visit_vec(&mut stc.fields, |field_def| self.visit_field_def(field_def));
                node_visitor::visit_vec(&mut stc.generics, |generic| self.visit_generic_param(generic));
            },
            ast::ItemKind::Function(function) => {
                self.resolution.define(DefinitonKind::Function, item.ident.clone(), item.node_id);
                node_visitor::visit_fn(function, self);
            },
            ast::ItemKind::GlobalVar(ty, expr, is_const) => {
                self.resolution.define(
                    if *is_const {DefinitonKind::Global} else {DefinitonKind::Const},
                    item.ident.clone(), item.node_id);
                self.visit_ty_expr(ty);
                node_visitor::visit_option(expr, |expr| self.visit_expr(expr));
            }
            ast::ItemKind::Err => ()
        } 
    }
}

#[derive(Default)]
struct Rib {
    symspace: HashMap<Symbol, Local>,
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
        if let Some(decl) = self.ribs.last().and_then(|rib| rib.symspace.get(&symbol)) {
            self.resolution.diagnostics
                .error(format!("redeclaration of local {name} here", name = symbol.get()))
                .with_span(name.span.clone());
            self.resolution.diagnostics
                .note(format!("previous declaration of {name} here", name = symbol.get()))
                .with_span(decl.span.clone());
            return;
        }
        let decl = Local {
            site,
            span: name.span.clone()
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
                    .with_span(ident.span.clone());
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
            .with_span(ident.span.clone());
        false
    }
}

impl<'r> MutVisitor for NameResolutionPass<'r> {
    fn visit_item(&mut self, item: &mut ast::Item) {
        match &mut item.kind {
            ast::ItemKind::Function(function) => {
                if function.generics.len() > 0 {
                    let first = function.generics.first().unwrap();
                    let last = function.generics.last().unwrap();
                    self.resolution.diagnostics
                        .fatal("function generics are not supported yet")
                        .with_span(first.span.start..last.span.end);
                }
                self.visit_ty_expr(&mut function.returns);

                let Some(ref mut body) = function.body else {
                    node_visitor::visit_vec(&mut function.params, |p| self.visit_param(p));
                    return;
                };

                self.with_rib(|this| {
                    node_visitor::visit_vec(&mut function.params, |p| this.visit_param(p));
                    node_visitor::visit_vec(body, |stmt| this.visit_stmt(stmt));
                });
            }
            ast::ItemKind::Struct(stc) => {
                if stc.generics.len() > 0 {
                    let first = stc.generics.first().unwrap();
                    let last = stc.generics.last().unwrap();
                    self.resolution.diagnostics
                        .fatal("struct generics are not supported yet")
                        .with_span(first.span.start..last.span.end);
                }
                node_visitor::visit_vec(&mut stc.fields, |field_def| self.visit_field_def(field_def));
            }
            ast::ItemKind::GlobalVar(ty, expr, _) => {
                self.visit_ty_expr(ty);
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
                    ast::PatternKind::Literal(..) => { 
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
            _ => noop_visit_stmt_kind(&mut stmt.kind, self),
        }
    }

    fn visit_expr(&mut self, expr: &mut ast::Expr) {
        match &mut expr.kind {
            ast::ExprKind::Name(name) => {
                self.resolve_priority(&[NameSpace::Variable, NameSpace::Function], name);
            }
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
                                self.visit_expr(expr),
                            ast::ArrayCapacity::Infer | ast::ArrayCapacity::Dynamic => ()
                        }
                    }
                    ast::TypeExprKind::Generic(..) => {
                        self.resolution.diagnostics
                            .fatal("generic types are not supported yet")
                            .with_span(ty.span.clone());
                    }
                    ast::TypeExprKind::Ref(..) | ast::TypeExprKind::Function { .. } =>
                        panic!("invalid state after parsing type init")
                }
            }
            ast::ExprKind::FunctionCall(base, args, generic_args) if matches!(&base.kind, ast::ExprKind::Name(..)) => {
                let ast::ExprKind::Name(name) = &mut base.kind else {
                    panic!();
                };
                if generic_args.len() > 0 {
                    self.resolution.diagnostics
                        .fatal("generic function calls are not supported yet")
                        .with_span(expr.span.clone());
                    return;
                }
                node_visitor::visit_vec(args, |arg| self.visit_argument(arg));
                self.resolve_priority(&[NameSpace::Function, NameSpace::Variable], name);
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
            ast::PatternKind::Literal(..) => {
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
                self.resolve(NameSpace::Type, name, true);
            },
            ast::TypeExprKind::Generic(..) => {
                self.resolution.diagnostics
                    .fatal("generic types are not supported yet")
                    .with_span(ty.span.clone());
            }
            ast::TypeExprKind::Function { .. } => {
                self.resolution.diagnostics
                    .fatal("function types are not supported yet")
                    .with_span(ty.span.clone());
            }
            ast::TypeExprKind::Array(base, cap) => {
                self.visit_ty_expr(base);
                match cap {
                    ast::ArrayCapacity::Discrete(expr) =>
                        self.visit_expr(expr),
                    ast::ArrayCapacity::Infer | ast::ArrayCapacity::Dynamic => ()
                }
            }
        }
    }
}

pub fn run_resolve(tree: &mut ast::TopLevel) {
    let mut resolution = ResolutionState::new(tree.diagnostics);

    let mut rpass = TypeResolutionPass::new(&mut resolution);
    rpass.resolve(tree);

    let mut rpass = NameResolutionPass::new(&mut resolution);
    rpass.visit(tree);
}

