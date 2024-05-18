use core::panic;
use std::cell::RefCell;
use std::collections::HashMap;
use std::marker::PhantomData;
use std::mem::transmute;
use std::ops::{Range, Deref, Index, IndexMut};

use crate::ast::{self as ast, NodeId, Ident, Resolution};
use crate::diagnostics::Diagnostics;
use crate::node_visitor::{
    MutVisitor, self as vis
};
use multimap::MultiMap;
use paste::paste;

macro_rules! make_node_genertor {
    ($fn_name:ident, $kind:ident) => {
        paste! {
            fn $fn_name<T: MakeNodeId>(kind: ast::[<$kind Kind>], ctx: &mut T) -> ast::$kind {
                let res = ast::$kind {
                    kind,
                    span: ast::DUMMY_SPAN,
                    node_id: ctx.make_node_id(None)
                };
                res
            }
        }
    };
}

trait MakeNodeId {
    fn make_node_id(&mut self, id: Option<&mut ast::NodeId>) -> NodeId;
}

#[derive(Debug, Clone, Copy)]
enum SymbolSpace {
    ValueSpace,
    TypeSpace,
    FunctionSpace
}

#[derive(Clone)]
struct NameBinding {
    kind: NameBindingKind,
    node_id: NodeId,
    span: Range<usize> // span for error diagnostics
}

#[derive(Clone)]
enum NameBindingKind {
    Definition(ast::Definiton),
    Imported
}

enum NamespaceKind<'a> {
    File(Diagnostics),
    Anonymous(Namespace<'a>)
}

pub struct NamespaceData<'a> {
    kind: NamespaceKind<'a>,

    type_resolutions: RefCell<HashMap<Ident, NameBinding>>,
    value_resolutions: RefCell<HashMap<Ident, NameBinding>>,
    function_resolutions: RefCell<MultiMap<Ident, NameBinding>>
}

#[derive(Clone, Copy)]
pub struct Namespace<'a>(&'a NamespaceData<'a>);

impl<'a> Deref for Namespace<'a> {
    type Target = NamespaceData<'a>;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

impl<'a> NamespaceData<'a> {
    fn new(kind: NamespaceKind<'a>) -> Self {
        Self {
            kind,

            type_resolutions: Default::default(),
            value_resolutions: Default::default(),
            function_resolutions: Default::default()    
        }
    }

    fn diagnostics(&self) -> Diagnostics {
        match self.kind {
            NamespaceKind::File(d) => d,
            NamespaceKind::Anonymous(parent) => parent.diagnostics(),
        }
    }
    
    fn update(&self, ident: ast::Ident, binding: NameBinding, space: SymbolSpace) -> Result<(), NameBinding> {
        let old_binding = match space {
            SymbolSpace::ValueSpace => self.value_resolutions.borrow_mut().insert(ident, binding),
            SymbolSpace::TypeSpace => self.type_resolutions.borrow_mut().insert(ident, binding),
            SymbolSpace::FunctionSpace => {
                self.function_resolutions.borrow_mut().insert(ident, binding);
                None
            }
        };
        if let Some(old_binding) = old_binding {
            return Err(old_binding);
        }
        Ok(())
    }

    fn define(&self, def: ast::Definiton, binding: (ast::Ident, NodeId, Range<usize>)) {
        let space = match def {
            ast::Definiton::Local | ast::Definiton::StaticVar |
            ast::Definiton::Const => SymbolSpace::ValueSpace,
            ast::Definiton::Struct => SymbolSpace::TypeSpace,
            ast::Definiton::Function => SymbolSpace::FunctionSpace
        };
        let ident = binding.0;
        let binding = NameBinding {
            kind: NameBindingKind::Definition(def),
            node_id: binding.1,
            span: binding.2
        };
        if let Err(old_binding) = self.update(ident.clone(), binding.clone(), space) {
            let space = match space {
                SymbolSpace::TypeSpace => "type",
                SymbolSpace::ValueSpace => "name",
                SymbolSpace::FunctionSpace => "function"
            };
            self.diagnostics()
                .error(format!("redefiniton of {space} `{name}`", name = ident.symbol.get()))
                .with_span(binding.span);
            self.diagnostics()
                .note(format!("`{name}` previously was defined here", name = ident.symbol.get()))
                .with_span(old_binding.span);
        }
    }
}

impl std::hash::Hash for Diagnostics {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_usize(unsafe {
            transmute::<Diagnostics, usize>(*self)
        });
    }
}

pub struct Resolver<'a> {
    namespace_arena: bumpalo::Bump,
    phantom: PhantomData<&'a u8>
}

impl<'a> Resolver<'a> {
    pub fn new() -> Self {
        let namespace_arena = bumpalo::Bump::new();

        Self {
            namespace_arena,
            phantom: PhantomData::default()
        }
    }

    fn resolve_impl(&mut self, unit: &mut ast::Unit, namespace: Namespace<'a>) {
        let mut visitor = ResolutionVisitor::new(self, namespace);
        visitor.visit_unit(unit);

        // resolve requested namespaces

        let mut visitor = LateResolutionVisitor::new(self, namespace);
        visitor.visit_unit(unit);
    }

    pub fn resolve_unit(&mut self, unit: &mut ast::Unit) {
        let namespace = make_namespace(&self.namespace_arena, NamespaceKind::File(unit.diagnostics));
        self.resolve_impl(unit, namespace);
    }
}

fn make_namespace<'b>(
    arena: &bumpalo::Bump, kind: NamespaceKind<'b>
) -> Namespace<'b> {
    let data = arena.alloc(NamespaceData::new(kind));
    let data = unsafe { transmute::<&mut NamespaceData, &'b NamespaceData>(data) };
    Namespace(data)
}

struct ResolutionVisitor<'a, 'res> {
    current_id: u32,
    resolver: &'a mut Resolver<'res>,
    namespace_stack: Vec<Namespace<'res>>
}

impl<'a, 'res> ResolutionVisitor<'a, 'res> {
    fn new(resolver: &'a mut Resolver<'res>, namespace: Namespace<'res>) -> Self {
        Self {
            current_id: 0,
            resolver,
            namespace_stack: vec![namespace] 
        }
    }

    fn current_namespace(&self) -> Namespace<'res> {
        let Some(ns) = self.namespace_stack.last() else {
            panic!("ResolutionVisitor: calling current_namespace without calling with_namespace (being in namespace context)");
        };
        return *ns;
    }

    fn _with_namespace<F: FnOnce(&mut Self)>(&mut self, namespace: Namespace<'res>, do_work: F) {
        self.namespace_stack.push(namespace);
        do_work(self);
        self.namespace_stack.pop();
    }

    fn define(&self, def: ast::Definiton, binding: (ast::Ident, NodeId, Range<usize>)) {
        self.current_namespace().define(def, binding);
    }

    fn path_to_attribute_lookups(&mut self, segments: &[ast::Ident], ident: ast::Ident) -> ast::Expr {
        let mut expr = {
            let ident = segments[0].clone();
            ast::Expr {
                span: ident.span.clone(),
                kind: ast::ExprKind::Name(ast::QName::Unresolved(ident)),
                node_id: self.make_node_id(None)
            }
        };

        for ident in segments[1..].iter() {
            expr = ast::Expr {
                span: (expr.span.start..ident.span.end),
                kind: ast::ExprKind::Attribute(Box::new(expr), ident.clone()),
                node_id: self.make_node_id(None)
            };
        }

        ast::Expr {
            span: (expr.span.start..ident.span.end),
            kind: ast::ExprKind::Attribute(Box::new(expr), ident),
            node_id: self.make_node_id(None)
        }
    }
}

impl<'a, 'res> MutVisitor for ResolutionVisitor<'a, 'res> {
    fn visit_unit(&mut self, unit: &mut ast::Unit) {
        vis::visit_vec(&mut unit.items, |item| self.visit_item(item));
    }

    fn visit_pattern(&mut self, pattern: &mut ast::Pattern) {  
        self.make_node_id(Some(&mut pattern.node_id));
        vis::noop_visit_pattern_kind(&mut pattern.kind, self);
    }

    fn visit_item(&mut self, item: &mut ast::Item) {
        self.make_node_id(Some(&mut item.node_id));
        vis::noop_visit_item_kind(&mut item.kind, self);
        match &mut item.kind {
            ast::ItemKind::Proc(..) => {
                self.define(
                        ast::Definiton::Function,
                        (item.ident.clone(), item.node_id, item.span.clone())
                    );
            }
            ast::ItemKind::Record(..) => {
                self.define(
                        ast::Definiton::Struct,
                        (item.ident.clone(), item.node_id, item.span.clone())
                    );
            }
            ast::ItemKind::StaticVar(..) => {
                self.define(
                        ast::Definiton::StaticVar,
                        (item.ident.clone(), item.node_id, item.span.clone())
                    );
            }
            ast::ItemKind::Constant(..) => {
                self.define(
                        ast::Definiton::Const,
                        (item.ident.clone(), item.node_id, item.span.clone())
                    );
            }
            ast::ItemKind::UseImport(path) => {
                self.current_namespace().diagnostics()
                    .error(format!("could not resolve namespace `{}`", path.segments[0].symbol.get()))
                    .with_span(item.span.clone());
            }
            ast::ItemKind::WithImport(qpath, _) => {
                let (path, _) = qpath.into();
                self.current_namespace().diagnostics()
                    .error(format!("could not resolve namespace `{}`", path.segments[0].symbol.get()))
                    .with_span(item.span.clone());
            }
            _ => unreachable!()
        }
    }

    fn visit_param(&mut self, param: &mut ast::Param) { 
        self.make_node_id(Some(&mut param.node_id));
        vis::noop_visit_param(param, self);
    }

    fn map_stmt(&mut self, mut stmt: ast::Stmt) -> Vec<ast::Stmt> {
        self.make_node_id(Some(&mut stmt.node_id));
        vis::noop_visit_stmt_kind(&mut stmt.kind, self);
        vec![stmt]
    }

    fn visit_expr(&mut self, expr: &mut ast::Expr) {
        vis::noop_visit_expr_kind(&mut expr.kind, self);
        match &mut expr.kind {
            ast::ExprKind::Path(qpath) => {
                let (path, ident) = qpath.into();
                *expr = self.path_to_attribute_lookups(&path.segments, ident);
            }
            _ => {
                self.make_node_id(Some(&mut expr.node_id));
            }
        }
    }

    fn visit_ty_expr(&mut self, ty: &mut ast::TypeExpr) {
        self.make_node_id(Some(&mut ty.node_id));
        vis::noop_visit_ty_expr_kind(&mut ty.kind, self);
    }

    fn visit_generic_param(&mut self, param: &mut ast::GenericParam) {
        self.make_node_id(Some(&mut param.node_id));
        vis::noop_visit_generic_param_kind(&mut param.kind, self);
    }
}

struct Rib<'a> {
    kind: RibKind<'a>,
    map: HashMap<Ident, Resolution>
}

impl<'a> Rib<'a> {
    fn new(kind: RibKind<'a>) -> Self {
        Self {
            kind,
            map: HashMap::new()
        }
    }
}

enum RibKind<'a> {
    Normal,
    Namespace(Namespace<'a>),
}

struct LateResolutionVisitor<'a, 'res> {
    type_ribs: Vec<Rib<'res>>,
    value_ribs: Vec<Rib<'res>>,
    function_ribs: Vec<Rib<'res>>,
    resolver: &'a mut Resolver<'res>,
    namespace: Namespace<'res>
}

impl<'a, 'res> Index<SymbolSpace> for LateResolutionVisitor<'a, 'res> {
    type Output = Vec<Rib<'res>>;
    fn index(&self, space: SymbolSpace) -> &Self::Output { 
        match space {
            SymbolSpace::ValueSpace => &self.value_ribs,
            SymbolSpace::TypeSpace => &self.type_ribs,
            SymbolSpace::FunctionSpace => &self.function_ribs
        }
    }
}

impl<'a, 'res> IndexMut<SymbolSpace> for LateResolutionVisitor<'a, 'res> {
    fn index_mut(&mut self, space: SymbolSpace) -> &mut Vec<Rib<'res>> {
        match space {
            SymbolSpace::ValueSpace => &mut self.value_ribs,
            SymbolSpace::TypeSpace => &mut self.type_ribs,
            SymbolSpace::FunctionSpace => &mut self.function_ribs
        }
    }
}

impl<'a, 'res> LateResolutionVisitor<'a, 'res> {
    fn new(resolver: &'a mut Resolver<'res>, namespace: Namespace<'res>) -> Self {
        Self {
            resolver,
            value_ribs: Vec::new(),
            type_ribs: Vec::new(),
            function_ribs: Vec::new(),
            namespace
        }
    }

    fn with_rib<F: FnOnce(&mut Self)>(&mut self, space: SymbolSpace, kind: RibKind<'res>, do_work: F) {
        self[space].push(Rib::new(kind));
        do_work(self);
        self[space].pop();
    }

    fn resolve_fn_params<'b>(&mut self, inputs: impl Iterator<Item = (&'b ast::Pattern, &'b ast::TypeExpr)>) {
        for _input in inputs {

        }
    }
}

impl<'a, 'res> MutVisitor for LateResolutionVisitor<'a, 'res> {
    fn visit_unit(&mut self, unit: &mut ast::Unit) {
        self.with_rib(SymbolSpace::TypeSpace, RibKind::Namespace(self.namespace), |this| {
            this.with_rib(SymbolSpace::ValueSpace, RibKind::Namespace(this.namespace), |this| {
                this.with_rib(SymbolSpace::FunctionSpace, RibKind::Namespace(this.namespace), |this| {
                    vis::visit_vec(&mut unit.items, |item| this.visit_item(item));
                });
            });
        });
    }

    fn visit_item(&mut self, item: &mut ast::Item) {
        match &mut item.kind {
            ast::ItemKind::Proc(proc) => {
                self.with_rib(SymbolSpace::ValueSpace, RibKind::Normal, |this| {
                    this.resolve_fn_params(proc.params.iter().map(|ast::Param { pat, ty, .. }| (pat, ty)));
                    vis::noop_visit_item_kind(&mut item.kind, this);
                });
            }
            _ => vis::noop_visit_item_kind(&mut item.kind, self)
        }
    }

    fn visit_expr(&mut self, expr: &mut ast::Expr) {
        vis::noop_visit_expr_kind(&mut expr.kind, self);
    }

    fn visit_ty_expr(&mut self, ty: &mut ast::TypeExpr) {
        vis::noop_visit_ty_expr_kind(&mut ty.kind, self);
    }
}

struct LoweringVisitor {
    current_id: u32
}

impl MutVisitor for LoweringVisitor {
    fn map_stmt(&mut self, stmt: ast::Stmt) -> Vec<ast::Stmt> {
        match stmt.kind {
            ast::StmtKind::While(condition, mut body) => {
                body.insert(0, while_synthesize_if(condition, self));
                vec![ast::Stmt {
                    kind: ast::StmtKind::Loop(body),
                    span: stmt.span,
                    node_id: stmt.node_id,
                }]
            },
            ast::StmtKind::For(var, iterator, mut body) => {
                let def_node_id = self.make_node_id(None);

                let (iterator_def, iterator_var) = make_definition(stmt.node_id, "iterator", def_node_id, self);

                body.splice(0..0, for_synthesize_stmts(var, iterator_var, self));
                vec![
                    ast::Stmt {
                        kind: ast::StmtKind::Local(
                            make_ident_pattern(iterator_def.0, iterator_def.1),
                            None, Some(iterator)),
                        span: ast::DUMMY_SPAN,
                        node_id: def_node_id
                    },
                    ast::Stmt {
                        kind: ast::StmtKind::Loop(body),
                        span: stmt.span,
                        node_id: stmt.node_id,
                    }
                ]
            }
            ast::StmtKind::Assign(lhs, rhs) if matches!(lhs.kind, ast::ExprKind::Tuple(..)) => {
                vec![desugar_tuple_assign_to_pattern(lhs, rhs, stmt.span, stmt.node_id, self)]
            }
            _ => vec![stmt]
        }
    }
}

fn desugar_tuple_assign_to_pattern(
    lhs: Box<ast::Expr>, rhs: Box<ast::Expr>,
    orig_span: Range<usize>, node_id: NodeId,
    ctx: &mut LoweringVisitor) -> ast::Stmt {
    let def_node_id = ctx.make_node_id(None);

    let elems = match lhs.kind {
        ast::ExprKind::Tuple(elems) => elems,
        _ => unreachable!()
    };
    let (defs, vars): (Vec<_>, Vec<_>) = (0..elems.len())
                       .map(|elem_idx| make_definition(node_id, format!("tpl.{elem_idx}").as_ref(), def_node_id, ctx))
                       .unzip();

    let mut body: Vec<_> = std::iter::zip(elems, vars).map(|(expr, var)| {
        let var = create_expr(ast::ExprKind::Name(var), ctx);
        if let ast::ExprKind::Tuple(..) = expr.kind {
            let span = expr.span.clone();
            let node_id = expr.node_id;
            desugar_tuple_assign_to_pattern(Box::new(expr), Box::new(var), span, node_id, ctx)
        } else {
            create_stmt(ast::StmtKind::Assign(Box::new(expr), Box::new(var)), ctx)
        }
    }).collect();

    body.insert(0,
        ast::Stmt {
            kind: ast::StmtKind::Local(
                create_pattern(
                    ast::PatternKind::Tuple(defs.into_iter().map(|(d, i)| make_ident_pattern(d, i)).collect()),
                    ctx),
                    None, Some(rhs)),
            span: ast::DUMMY_SPAN,
            node_id: def_node_id
        }
    );

    ast::Stmt {
        kind: ast::StmtKind::Block(body),
        span: orig_span,
        node_id,
    }
}

fn for_synthesize_stmts(pattern: ast::Pattern, iterator_var: ast::QName, ctx: &mut LoweringVisitor) -> Vec<ast::Stmt> {
    let has_next_call = create_function_call(
        ast::Ident::from_str("HasNext"),
        vec![create_expr(ast::ExprKind::Name(iterator_var.clone()), ctx)], ctx);

    let next_call = create_function_call(
        ast::Ident::from_str("Next"),
        vec![create_expr(ast::ExprKind::Name(iterator_var), ctx)], ctx);

    vec![
        create_stmt(ast::StmtKind::If(
                Box::new(has_next_call),
                vec![create_stmt(ast::StmtKind::ControlFlow(ast::ControlFlow::Break), ctx)],
                None),
            ctx),
        create_stmt(ast::StmtKind::Local(
                pattern, None,
                Some(Box::new(next_call))),
            ctx),
    ]
}

fn while_synthesize_if(condition: Box<ast::Expr>, ctx: &mut LoweringVisitor) -> ast::Stmt {
    create_stmt(ast::StmtKind::If(
        condition,
        vec![create_stmt(ast::StmtKind::ControlFlow(ast::ControlFlow::Break), ctx)],
        None),
    ctx)
}

fn create_function_call(function: ast::Ident, args: Vec<ast::Expr>, ctx: &mut LoweringVisitor) -> ast::Expr {
    let function = create_expr(ast::ExprKind::Name(ast::QName::Unresolved(function)), ctx);
    let args = args.into_iter().map(|arg| ast::FunctionArgument::Direct(Box::new(arg))).collect();
    create_expr(ast::ExprKind::FunctionCall(Box::new(function), args), ctx)
}

make_node_genertor!(create_stmt, Stmt);
make_node_genertor!(create_expr, Expr);
make_node_genertor!(create_pattern, Pattern);

fn make_ident_pattern(ident: ast::Ident, def_id: NodeId) -> ast::Pattern {
    ast::Pattern {
        kind: ast::PatternKind::Ident(ident),
        span: ast::DUMMY_SPAN,
        node_id: def_id
    }
}

fn make_definition(id: ast::NodeId, ident: &str, def_node_id: NodeId, ctx: &mut LoweringVisitor) -> ((ast::Ident, ast::NodeId), ast::QName) {
    let def_id = ctx.make_node_id(None); 

    let ident = ast::Ident::from_str(format!("<{ident}-{id}>", id=id.0).as_ref());
    let var = ast::QName::Resolved {
        ident: ident.clone(), 
        res: ast::Resolution::Definition(ast::Definiton::Local),
        node_id: def_node_id,
    };

    ((ident, def_id), var)
}

macro_rules! make_make_node_id {
    () => {    
        fn make_node_id(&mut self, id: Option<&mut ast::NodeId>) -> NodeId {
            match id {
                Some(&mut ast::NODE_ID_UNDEF) => {
                    let rv = ast::NodeId(self.current_id);
                    self.current_id += 1;
                    *id.unwrap() = rv.clone();
                    rv
                }
                Some(&mut node_id) => node_id.clone(),
                None => {
                    let rv = ast::NodeId(self.current_id);
                    self.current_id += 1;
                    rv
                }
            }
        }
    };
}

impl<'a, 'res> MakeNodeId for ResolutionVisitor<'a, 'res> {
    make_make_node_id!();
}

impl MakeNodeId for LoweringVisitor {
    make_make_node_id!();
}

