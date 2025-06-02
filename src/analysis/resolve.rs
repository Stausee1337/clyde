
use std::{collections::VecDeque, fmt::Write, io, path::{Path, PathBuf}, rc::Rc, str::FromStr};

use foldhash::quality::RandomState;
use hashbrown::{self, HashMap, hash_map::Entry};
use index_vec::IndexVec;
use sha1::Digest;

use crate::{context::TyCtxt, diagnostics::{DiagnosticsCtxt, Message}, files, session::Session, syntax::{ast::{self, DefId, DefinitionKind, IntoNode, NodeId, OutsideScope, Resolution}, lexer::Span, parser, symbol::{sym, Symbol}}};
use super::node_visitor::{self, Visitor};

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

impl TryFrom<DefinitionKind> for NameSpace {
    type Error = ();

    fn try_from(value: DefinitionKind) -> Result<Self, ()> {
        use DefinitionKind as D;
        Ok(match value {
            D::Struct | D::Enum | D::ParamTy | D::TypeAlias => NameSpace::Type,
            D::Function => NameSpace::Function,
            D::Static | D::Const | D::ParamConst => NameSpace::Variable,
            _ => return Err(())
        })
    }
}

#[derive(Clone, Copy)]
struct Declaration {
    site: ast::DefId,
    scope: ast::Scope,
    kind: DefinitionKind,
    span: Span,
}

#[derive(Clone)]
struct Local {
    site: NodeId,
    span: Span,
}

enum DefParentOrInfer {
    DefParent(DefParent),
    Infer(NodeId)
}

#[derive(Clone, Copy)]
pub enum DefParent {
    Definition(DefId),
    SourceFile(NodeId),
}

pub struct Definition {
    pub node: NodeId,
    pub kind: DefinitionKind,
    pub parent: DefParent
}

struct ResolutionState<'tcx> {
    items: Vec<ast::DefId>,
    file_cacher: Rc<files::FileCacher>,
    diagnostics: &'tcx DiagnosticsCtxt,
    rib_map: HashMap<NodeId, TFGRib>,
    node_to_path_map: HashMap<NodeId, PathBuf>,
    mangled_names: HashMap<NodeId, Symbol>,
    declarations: index_vec::IndexVec<ast::DefId, Definition>,
    inner_items: HashMap<DefId, Vec<(DefId, DefinitionKind)>>,
    ast_info: &'tcx ast::AstInfo<'tcx>,
}

pub struct ResolutionResults<'tcx> {
    pub ast_info: &'tcx ast::AstInfo<'tcx>,
    pub items: Vec<ast::DefId>,
    pub entry: Option<ast::DefId>,
    pub declarations: index_vec::IndexVec<ast::DefId, Definition>,
    pub node_to_path_map: HashMap<NodeId, PathBuf>,
    pub mangled_names: HashMap<NodeId, Symbol>,
    pub inner_items: HashMap<DefId, Vec<(DefId, DefinitionKind)>>
}

impl<'tcx> ResolutionState<'tcx> {
    fn new(session: &'tcx Session, ast_info: &'tcx ast::AstInfo<'tcx>) -> ResolutionState<'tcx> {
        let file_cacher = session.file_cacher();
        let diagnostics = session.diagnostics();
        ResolutionState {
            diagnostics,
            file_cacher,
            items: Default::default(),
            rib_map: Default::default(),
            node_to_path_map: Default::default(),
            mangled_names: Default::default(),
            declarations: Default::default(),
            inner_items: Default::default(),
            ast_info
        }
    }

    fn results(self, entry: NodeId) -> ResolutionResults<'tcx> {
        let entry_module = &self.rib_map[&entry];
        let entry = entry_module.functions.get(&sym::main).map(|decl| decl.site); 
        ResolutionResults {
            ast_info: self.ast_info,
            items: self.items, entry,
            declarations: self.declarations,
            node_to_path_map: self.node_to_path_map,
            mangled_names: self.mangled_names,
            inner_items: self.inner_items
        }
    }
}

#[derive(Clone, Copy)]
enum ModuleImport {
    Unresolved {
        file: FileId,
        span: Span
    },
    Resolved(Result<NodeId, ()>),
}

impl ModuleImport {
    fn span(&self) -> Span {
        let ModuleImport::Unresolved { span, .. } = self else {
            unreachable!("wrong phase for diagnostics");
        };
        *span
    }
}

/// Types, Functions, Globals Rib
struct TFGRib {
    parent: DefParent,
    types: HashMap<Symbol, Declaration>,
    functions: HashMap<Symbol, Declaration>,
    globals: HashMap<Symbol, Declaration>,
    modules: HashMap<Symbol, ModuleImport>,
    pending_imports: Vec<ModuleImport>,
}

impl TFGRib {
    fn new(parent: DefParent) -> Self {
        Self {
            parent,
            types: Default::default(),
            functions: Default::default(),
            globals: Default::default(),
            modules: Default::default(),
            pending_imports: Default::default()
        }
    }

    fn get_exports(&self) -> (Vec<(Symbol, Declaration)>, Vec<(Symbol, Declaration)>, Vec<(Symbol, Declaration)>) {
        macro_rules! for_scope {
            ($scope:ident) => {        
                self.$scope
                    .iter()
                    .filter_map(|(sym, decl)| match decl.scope {
                        ast::Scope::Export => Some((*sym, *decl)),
                        ast::Scope::Module => None,
                    })
                    .collect::<Vec<_>>()
            };
        }
        let types = for_scope!(types);
        let functions = for_scope!(functions);
        let globals = for_scope!(globals);
        (types, functions, globals)
    }

    fn import(
        &mut self,
        (types, functions, globals): (Vec<(Symbol, Declaration)>, Vec<(Symbol, Declaration)>, Vec<(Symbol, Declaration)>),
        span: Span,
        diagnostics: &DiagnosticsCtxt,
    ) {
        macro_rules! for_scope {
            ($scope:ident) => {
                for (symbol, mut declaration) in $scope {
                    declaration.span = span;
                    self.define_with_declaration(symbol, declaration, diagnostics);
                }         
            };
        }
        for_scope!(types);
        for_scope!(functions);
        for_scope!(globals);
    }

    fn define(
        &mut self,
        kind: DefinitionKind,
        name: ast::Ident,
        site: NodeId,
        scope: ast::Scope,
        resolution: &mut ResolutionState
    ) -> ast::DefId {
        let declaration = Declaration {
            scope,
            site: resolution.declarations.push(Definition {
                node: site,
                kind,
                parent: self.parent
            }), 
            kind,
            span: name.span
        };
        let site = declaration.site;
        resolution.items.push(site);
        self.define_with_declaration(name.symbol, declaration, resolution.diagnostics);
        site
    }

    // FIXME: `define_with_declaration` and `define_aliased_module` share common code, so this
    // duplication should be removed 
    fn define_with_declaration(&mut self, symbol: Symbol, declaration: Declaration, diagnostics: &DiagnosticsCtxt) {
        let kind = declaration.kind;
        let space = match kind {
            DefinitionKind::Struct | DefinitionKind::Enum | DefinitionKind::ParamTy | DefinitionKind::TypeAlias => &mut self.types,
            DefinitionKind::Function => &mut self.functions,
            DefinitionKind::Static | DefinitionKind::Const | DefinitionKind::ParamConst => &mut self.globals,
            _ => unreachable!("invalid Definition in define")
        };
        // FIXME: use `HashMap::entry`
        if let Some(prev) = space.insert(symbol, declaration) {
            let namespace: NameSpace = kind.try_into()
                .expect("invalid Definition in define");
            Message::error(format!("redeclaration of {namespace} {name:?}", name = symbol.get()))
                .at(declaration.span)
                .hint(format!("previous declaration of {name:?} here", name = symbol.get()), prev.span)
                .push(diagnostics);
            space.insert(symbol, prev);
        }
    }

    fn define_aliased_module(&mut self, symbol: Symbol, import: ModuleImport, diagnostics: &DiagnosticsCtxt) {
        // FIXME: use `HashMap::entry`
        if let Some(prev) = self.modules.insert(symbol, import) {
            Message::error(format!("redeclaration of module alias {name:?}", name = symbol.get()))
                .at(import.span())
                .hint(format!("previous declaration of {name:?} here", name = symbol.get()), prev.span())
                .push(diagnostics);
            self.modules.insert(symbol, prev);
        }
    }

    fn add_pending_import(&mut self, import: ModuleImport) {
        self.pending_imports.push(import);
    }
}

index_vec::define_index_type! {
    struct FileId = u32;
}

#[derive(Debug)]
enum CollectionState<'tcx> {
    Pending,
    Resolved(&'tcx ast::SourceFile<'tcx>),
    Erroneous,
}

struct EarlyCollectionPass<'r, 'tcx> {
    resolution: &'r mut ResolutionState<'tcx>,
    ribs: Vec<TFGRib>,
    queue: VecDeque<FileId>,
    current_file: Option<&'tcx ast::SourceFile<'tcx>>,
    filemap: indexmap::IndexSet<PathBuf, RandomState>,
    file_collection_state: HashMap<FileId, CollectionState<'tcx>>,

    // mangling related attributes
    root_hash: String,
    root_path: PathBuf,
    root_file: String
}

impl<'r, 'tcx> EarlyCollectionPass<'r, 'tcx> {
    fn new(resolution: &'r mut ResolutionState<'tcx>) -> Self {
        Self {
            ribs: vec![],
            queue: Default::default(),
            resolution,
            current_file: None,
            filemap: Default::default(),
            file_collection_state: Default::default(),

            root_hash: String::new(),
            root_path: PathBuf::new(),
            root_file: String::new(),
        }
    }

    fn mangle_module_name(&mut self, module: &'tcx ast::SourceFile<'tcx>) {
        let node = module.node_id;
        let module = self.get_path(module).to_owned();
        let mut common_components = 0;
        for (a, b) in std::iter::zip(self.root_path.components(), module.components()) {
            if a != b {
                panic!("{module:?} is not relative to {:?}, wich is currently not supported", self.root_path);
            }
            common_components += 1;
        }
        let mut relative_path = PathBuf::new();
        relative_path.extend(module.components().skip(common_components));
        relative_path.set_extension("");
        let mut mangled_name = format!("_clyH{}{}F{}{}_", self.root_hash.len(), self.root_hash, self.root_file.len(), self.root_file);
        for comp in relative_path.components() {
            let component = comp.as_os_str().to_string_lossy();
            let component = component.replace(|ch: char| !ch.is_alphanumeric(), "_");
            write!(mangled_name, "{}", component.len()).unwrap();
            mangled_name.push_str(&component);
        }

        let mangled_name = Symbol::intern(&mangled_name);
        self.resolution.mangled_names.insert(node, mangled_name);
    }

    fn mangle_item_name(&mut self, item: &'tcx ast::Item<'tcx>) {
        let mut node = item.into_node();
        {
            let owners = self.resolution.ast_info.global_owners.borrow();
            loop {
                if let ast::Node::SourceFile(..) = node {
                    break;
                }
                node = owners[node.node_id().owner].node;
            }
        }
        let mangled_file_name = self.resolution.mangled_names[&node.node_id()];
        let ident = item.ident();
        let name = ident.symbol.get();
        let name = format!("{}{}{}", mangled_file_name.get(), name.len(), name);
        self.resolution.mangled_names.insert(item.node_id, Symbol::intern(&name));
    }

    fn get_path(&mut self, module: &'tcx ast::SourceFile<'tcx>) -> &Path {
        let file_cacher = self.resolution.file_cacher.clone();
        match self.resolution.node_to_path_map.entry(module.node_id) {
            Entry::Vacant(entry) => {
                let file = file_cacher.lookup_file(module.span.start);
                let path = file.path().canonicalize().unwrap();
                entry.insert(path)
            }
            Entry::Occupied(entry) =>
                entry.into_mut()
        }
    }

    fn normalize_path(&mut self, relative: &'tcx ast::SourceFile<'tcx>, segment: &str) -> Result<PathBuf, io::Error> {
        let path = PathBuf::from_str(segment).unwrap();
        if path.is_absolute() {
            return path.canonicalize();
        }

        let mut relative_path = self.get_path(relative).to_owned();
        relative_path.pop();
        relative_path.push(path);
        relative_path.canonicalize()
    }

    fn push_import(&mut self, relative: &'tcx ast::SourceFile<'tcx>, segment: &str, alias: Option<Symbol>, span: Span) {
        let path = self.normalize_path(relative, segment)
            .map_err(|err| {
                Message::error(format!("cannot import file: {segment}: {err}"))
                    .at(span)
                    .push(self.resolution.diagnostics);
            });

        let rib = self.ribs.last_mut().expect(".push_import neeeds to be called in valid TFGRib");
        let Ok(path) = path else {
            if let Some(symbol) = alias {
                let import = ModuleImport::Resolved(Err(()));
                rib.define_aliased_module(symbol, import, self.resolution.diagnostics);
            }
            return;
        };

        let (file, _) = self.filemap.insert_full(path);
        let file = FileId::from_usize(file);

        let import = ModuleImport::Unresolved { file, span };
        if let Some(symbol) = alias {
            rib.define_aliased_module(symbol, import, self.resolution.diagnostics);
        } else {
            rib.add_pending_import(import);
        }

        if let Some(..) = self.file_collection_state.get(&file) {
            return;
        }
        self.queue.push_back(file);
        self.file_collection_state.insert(file, CollectionState::Pending);
    }

    fn collect_bfs(
        mut self, 
        entry: &'tcx ast::SourceFile<'tcx>,
        session: &'tcx Session,
        ast_info: &'tcx ast::AstInfo<'tcx>,
    ) -> Vec<&'tcx ast::SourceFile<'tcx>> {
        let path = self.get_path(entry).to_owned();
        
        {
            self.root_path.push(&path);
            self.root_path.pop();

            let mut sha1 = sha1::Sha1::default();
            for component in self.root_path.components() {
                let bytes = component.as_os_str().as_encoded_bytes();
                sha1.update(bytes);
            }

            let mut root_hash = [0u8; 8];

            let hash = sha1.finalize();
            root_hash.copy_from_slice(&hash[0..8]);

            self.root_hash = base62::encode(u64::from_le_bytes(root_hash));

            let mut file_name = PathBuf::from(path.file_name().unwrap());
            file_name.set_extension("");
            let component = file_name.as_os_str().to_string_lossy();
            let component = component.replace(|ch: char| !ch.is_alphanumeric(), "_");

            self.root_file = component;
        }

        self.visit(entry);

        let (file, _) = self.filemap.insert_full(path);
        let file = FileId::from_usize(file);
        self.file_collection_state.insert(file, CollectionState::Resolved(entry));

        let mut file_to_node_map: HashMap<FileId, NodeId> = HashMap::default();

        while let Some(file) = self.queue.pop_front() {
            let path = &self.filemap[file.index()];
            let module = match parser::parse_file(session, path, ast_info) {
                Ok(module) => module,
                Err(()) => {
                    self.file_collection_state.insert(file, CollectionState::Erroneous);
                    continue;
                }
            };

            self.visit(module);

            self.file_collection_state.insert(file, CollectionState::Resolved(module));
            file_to_node_map.insert(file, module.node_id);
        }

        let ribs = self
            .resolution
            .rib_map
            .keys()
            .map(|id| *id)
            .collect::<Vec<_>>();

        for rib in &ribs {
            do_stuff(&file_to_node_map, &mut self.resolution.rib_map, *rib, self.resolution.diagnostics);
        }

        fn do_stuff(file_to_node_map: &HashMap<FileId, NodeId>, rib_map: &mut HashMap<NodeId, TFGRib>, node: NodeId, diagnostics: &DiagnosticsCtxt) {
            // This works, and won't loop on recursive imports, but it also doesn't handle them
            // fully correctly, if e.g.:
            // File A depends on File B and File C
            // File B depends on File A
            // Then File B should include all of File C, but this won't happen since we already
            // stop importing into File B once we see it depends on File A. File C will still be
            // imported into File A later. The trivial fix for this (in your code) is to just
            // import File C before File B in File A, but this is not always doable. In the long
            // run, recusrive imports should be identified here and resolved in multiple steps.
            let rib = rib_map.get_mut(&node).unwrap();
            let pending_imports = std::mem::replace(&mut rib.pending_imports, vec![]);

            for import in pending_imports {
                let ModuleImport::Unresolved { file, span } = import else {
                    unreachable!("Resolved Import can't be pending")
                };

                let Some(dependency_node) = file_to_node_map.get(&file).map(|id| *id) else {
                    continue;
                };
                do_stuff(file_to_node_map, rib_map, dependency_node, diagnostics);

                let dependency_rib = &rib_map[&dependency_node];
                let exports = dependency_rib.get_exports();
                
                let rib = rib_map.get_mut(&node).unwrap();
                rib.import(exports, span, diagnostics);
            }
        }

        for node in &ribs {
            let rib = self.resolution.rib_map.get_mut(node).unwrap();
            for import in rib.modules.values_mut() {
                let ModuleImport::Unresolved { file, .. } = *import else {
                    continue;
                };

                *import = ModuleImport::Resolved(file_to_node_map.get(&file).map(|id| *id).ok_or(()));
            }
        }
        
        let modules = self.file_collection_state
            .iter()
            .filter_map(|(_, module)| match module {
                CollectionState::Resolved(module) => Some(*module),
                CollectionState::Erroneous => None,
                CollectionState::Pending =>
                    unreachable!("CollectionState::Pending is invalid at name resolution")
            })
            .collect::<Vec<_>>();

        modules
    }

    fn define(&mut self, kind: DefinitionKind, name: ast::Ident, site: NodeId, scope: ast::Scope) -> ast::DefId {
        let rib = self.ribs.last_mut().expect(".define neeeds to be called in valid TFGRib");
        rib.define(kind, name, site, scope, self.resolution)
    }

    fn declare(&mut self, node: NodeId, kind: DefinitionKind) -> ast::DefId {
        let rib = self.ribs.last().expect(".declare neeeds to be called in valid TFGRib");
        self.resolution.declarations.push(Definition {
            node,
            kind,
            parent: rib.parent
        })
    }

    fn with_rib<F: FnOnce(&mut Self)>(&mut self, parent: DefParentOrInfer, do_work: F) {
        // test::instantiation_test<T>(int)::InnerStruct
        let (parent, node) = match parent {
            DefParentOrInfer::DefParent(parent) => (parent, None),
            DefParentOrInfer::Infer(node_id) => {
                let rib = self.ribs.last()
                    .expect("DefParent can only be inferred in cases where there already is a parent");
                (rib.parent, Some(node_id))
            }
        };
        self.ribs.push(TFGRib::new(parent));
        do_work(self);
        let rib = self.ribs.pop().unwrap();
        let node = node.unwrap_or_else(|| match parent {
            DefParent::Definition(def_id) =>
                self.resolution.declarations[def_id].node,
            DefParent::SourceFile(node_id) => node_id
        });
        if let Some(_) = self.resolution.rib_map.insert(node, rib) {
            panic!("tried to collect same rib twice {node:?}");
        }
    }
}

impl<'r, 'tcx> Visitor<'tcx> for EarlyCollectionPass<'r, 'tcx> {
    fn visit(&mut self, tree: &'tcx ast::SourceFile<'tcx>) {
        self.current_file.replace(tree);
        self.mangle_module_name(tree);
        self.with_rib(DefParentOrInfer::DefParent(DefParent::SourceFile(tree.node_id)), |this| {
            node_visitor::visit_slice(tree.items, |item| this.visit_item(item));
        });
        self.current_file.take();
    }

    fn visit_expr(&mut self, expr: &'tcx ast::Expr<'tcx>) {
        match &expr.kind {
            ast::ExprKind::Block(block) => {
                self.with_rib(DefParentOrInfer::Infer(expr.node_id), |this| {
                    this.visit_block(block);
                });
            }
            expr_kind => node_visitor::noop_visit_expr_kind(expr_kind, self),
        }
    }

    fn visit_generic_param(&mut self, param: &'tcx ast::GenericParam<'tcx>) {
        let site = match param.kind {
            ast::GenericParamKind::Type(name) =>
                self.define(DefinitionKind::ParamTy, name, param.node_id, ast::Scope::Export),
            ast::GenericParamKind::Const(name, _) => 
                self.define(DefinitionKind::ParamConst, name, param.node_id, ast::Scope::Export),
        };
        let _ = param.def_id.set(site);
    }

    fn visit_item(&mut self, item: &'tcx ast::Item<'tcx>) {
        match &item.kind {
            ast::ItemKind::Struct(stc) => {
                let site = self.define(DefinitionKind::Struct, stc.ident, item.node_id, item.scope);
                let _ = item.def_id.set(site);
                self.with_rib(DefParentOrInfer::DefParent(DefParent::Definition(site)), |this| {
                    node_visitor::visit_slice(&stc.generics, |generic| this.visit_generic_param(generic));
                    node_visitor::visit_slice(stc.fields, |field_def| this.visit_field_def(field_def));
                    node_visitor::visit_slice(&stc.items, |item| this.visit_item(item));
                });
            }, 
            ast::ItemKind::Enum(en) => {
                let site = self.define(DefinitionKind::Enum, en.ident, item.node_id, item.scope);
                let _ = item.def_id.set(site);
                self.with_rib(DefParentOrInfer::DefParent(DefParent::Definition(site)), |this| {
                    node_visitor::visit_slice(en.variants, |variant_def| this.visit_variant_def(variant_def));
                });
            },
            ast::ItemKind::Function(function) => {
                let site = self.define(DefinitionKind::Function, function.ident, item.node_id, item.scope);
                let _ = item.def_id.set(site);
                self.with_rib(DefParentOrInfer::DefParent(DefParent::Definition(site)), |this| {
                    node_visitor::visit_fn(function, this);
                });
            },
            ast::ItemKind::GlobalVar(global) => {
                let site = self.define( 
                    if global.constant {DefinitionKind::Const} else {DefinitionKind::Static},
                    global.ident, item.node_id, item.scope);
                let _ = item.def_id.set(site);
                node_visitor::visit_option(global.ty, |ty| self.visit_ty_expr(ty));
                node_visitor::visit_option(global.init, |expr| self.visit_expr(expr));
            }
            ast::ItemKind::Import(import) => {
                let file = self.current_file.expect("visit_import should be operating within source file");
                self.push_import(file, &import.path, None, item.span);
                return;
            }
            ast::ItemKind::Alias(alias) => {
                match alias.kind {
                    ast::AliasKind::Import(import) => {
                        let file = self.current_file.expect("visit_import should be operating within source file");
                        self.push_import(file, &import.path, Some(alias.ident.symbol), item.span);
                        return; // don't mangle the names of Import aliases
                    }
                    ast::AliasKind::Type(ty) => {
                        let site = self.define(DefinitionKind::TypeAlias, alias.ident, item.node_id, item.scope);
                        self.with_rib(DefParentOrInfer::DefParent(DefParent::Definition(site)), |this| {
                            node_visitor::visit_slice(&alias.generics, |generic| this.visit_generic_param(generic));
                            this.visit_ty_expr(ty);
                        });
                    }
                    ast::AliasKind::Err => ()
                }
            }
            ast::ItemKind::Err => return
        }
        self.mangle_item_name(item);
    }

    fn visit_field_def(&mut self, field_def: &'tcx ast::FieldDef<'tcx>) {
        self.visit_ty_expr(field_def.ty);
        node_visitor::visit_option(field_def.default_init, |default_init| self.visit_expr(default_init));
        field_def.def_id.set(self.declare(field_def.node_id, DefinitionKind::Field)).unwrap();
    }

    fn visit_variant_def(&mut self, variant_def: &'tcx ast::VariantDef<'tcx>) {
        node_visitor::visit_option(variant_def.discriminant, |sset| self.visit_nested_const(sset));
        variant_def.def_id.set(self.declare(variant_def.node_id, DefinitionKind::Variant)).unwrap();
    }

    fn visit_nested_const(&mut self, expr: &'tcx ast::NestedConst<'tcx>) {
        self.visit_expr(expr.expr);
        expr.def_id.set(self.declare(expr.node_id, DefinitionKind::NestedConst)).unwrap();
    }
}

#[derive(Default)]
struct LocalRib {
    symspace: HashMap<Symbol, Local>,
}

bitflags::bitflags! {
#[derive(Clone, Copy)]
struct SearchFlags: u32 {
    const VARIABLES = 1;
    const FUNCTIONS = 2;
    const TYPES     = 4;
    const MODULES   = 8;
}
}

#[derive(Default)]
enum ValueModuleResolution {
    Value(Resolution),
    Module(Result<NodeId, ()>),
    #[default]
    Empty
}

enum PathResolutionError {
    /// Not a real error, the rest of the resolution needs to be done at typecheck stage
    Barrier,
    /// The last segment could not be resolved
    End(Span),
    /// An Error was already emitted
    Emitted
}

struct NameResolutionPass<'r, 'tcx> {
    resolution: &'r mut ResolutionState<'tcx>,
    ribs: Vec<LocalRib>,
    tfg_ribs: Vec<NodeId>,
    loop_owners: Vec<NodeId>
}

impl<'r, 'tcx> NameResolutionPass<'r, 'tcx> {
    fn new(resolution: &'r mut ResolutionState<'tcx>) -> Self {
        Self {
            resolution,
            ribs: Default::default(),
            tfg_ribs: Default::default(),
            loop_owners: Vec::new()
        }
    }

    fn resolve(&mut self, modules: Vec<&'tcx ast::SourceFile<'tcx>>) {
        for module in modules {
            self.visit(module);
        }
    }

    fn with_tfg_rigb<F: FnOnce(&mut Self)>(&mut self, node: NodeId, do_work: F) {
        let Some(..) = self.resolution.rib_map.get(&node) else {
            panic!("{node:?} at doesn't have a TFGRib associated at name resolution");
        };
        self.tfg_ribs.push(node);
        do_work(self);
        self.tfg_ribs.pop().unwrap();
    }

    fn with_rib<F: FnOnce(&mut Self)>(&mut self, do_work: F) {
        self.ribs.push(LocalRib::default());
        do_work(self);
        self.ribs.pop().unwrap();
    }

    fn enter_loop_ctxt<F: FnOnce(&mut Self)>(&mut self, owner: NodeId, do_work: F) {
        self.loop_owners.push(owner);
        do_work(self);
        self.loop_owners.pop();
    }

    fn has_rib(&self) -> bool {
        self.ribs.len() > 0
    }

    fn define(&mut self, name: ast::Ident, site: NodeId) {
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

    fn resolve_in_tfg_rib(&self, node: &NodeId, symbol: Symbol, flags: SearchFlags) -> (tinyvec::ArrayVec<[ValueModuleResolution; 3]>, SearchFlags) {
        let rib = &self.resolution.rib_map[node];
        let spaces = [
            (SearchFlags::VARIABLES, &rib.globals),
            (SearchFlags::FUNCTIONS, &rib.functions),
            (SearchFlags::TYPES, &rib.types),
        ];
        let mut results: tinyvec::ArrayVec<[ValueModuleResolution; 3]> = Default::default();
        let mut found = SearchFlags::empty();
        for (flag, space) in spaces {
            if !flags.contains(flag) {
                continue;
            }
            if let Some(decl) = space.get(&symbol) {
                results.push(ValueModuleResolution::Value(Resolution::Def(decl.site, decl.kind)));
                found |= flag;
            }
        }
        if flags.contains(SearchFlags::MODULES) {   
            if let Some(ModuleImport::Resolved(module)) = rib.modules.get(&symbol) {
                results.push(ValueModuleResolution::Module(*module));
                found |= SearchFlags::MODULES;
            }
        }
        (results, found)
    }

    fn resolve_path_segment(
        &mut self,
        segments: &'tcx [ast::PathSegment<'tcx>],
        rib_stack: &[NodeId],
        hit_a_barrier: bool,
        in_local_space: bool
    ) -> Option<Vec<ValueModuleResolution>> {
        if matches!(segments[0].ident, None) || hit_a_barrier {
            let segment = &segments[0];
            for arg in segment.generic_args {
                self.visit_generic_argument(arg);
            }
            return None;
        }

        let mut flags = SearchFlags::all();
        if segments.len() > 1 {
            flags.remove(SearchFlags::VARIABLES);
        }

        if segments[0].generic_args.len() > 0 {
            flags.remove(SearchFlags::VARIABLES);
            flags.remove(SearchFlags::MODULES);
        }

        let ident = segments[0].ident.unwrap();
        let mut results = vec![];

        if flags.contains(SearchFlags::VARIABLES) {
            if let Some(local) = self.resolve_local(ident.symbol) && in_local_space {
                results.push(ValueModuleResolution::Value(Resolution::Local(local.site)));
                flags.remove(SearchFlags::VARIABLES);
            }
        }

        for rib in rib_stack {
            let (resolution, found) = self.resolve_in_tfg_rib(rib, ident.symbol, flags);
            results.extend(resolution);
            flags.remove(found);

            if flags.is_empty() {
                break;
            }
        }

        if flags.contains(SearchFlags::TYPES) && in_local_space && ident.symbol.is_primitive_ty() {
            results.push(ValueModuleResolution::Value(Resolution::Primitive(ident.symbol)));
        }

        if segments[0].generic_args.len() > 0 {
            let segment = &segments[0];
            let Some(resolution) = results.get_resolution() else {
                return Some(results);
            };
            segment.resolve(resolution);
            for arg in segment.generic_args {
                self.visit_generic_argument(arg);
            }
            return None;
        }

        Some(results)
    }

    fn resolve_path(&mut self, path: &'tcx ast::Path<'tcx>) -> Result<Vec<Resolution>, PathResolutionError> {
        let mut node_id;

        let mut segments = path.segments;
        let tfg_ribs = self.tfg_ribs.clone();
        let mut rib_stack: &[NodeId] = &tfg_ribs;
        let mut in_local_space = true;
        let mut hit_a_barrier = false;

        let mut prev: Option<ast::Ident> = None;
        while segments.len() > 0 {
            let Some(results) = self.resolve_path_segment(segments, rib_stack, hit_a_barrier, in_local_space) else {
                hit_a_barrier = true;
                prev = segments[0].ident;
                segments = &segments[1..];
                in_local_space = false;
                continue;
            };

            if segments.len() > 1 {
                if let Some(module) = results.get_module() {
                    node_id = module.map_err(|_| PathResolutionError::Emitted)?;
                    rib_stack = std::slice::from_ref(&node_id);
                } else if let Some(resolution) = results.get_resolution() {
                    segments[0].resolve(resolution);
                    break; // after we've got a resolution here, typecheck stage will need to
                           // figure out what do with it
                }
            } else if !results.is_empty() {
                let results = results
                    .iter()
                    .filter_map(|res| match res {
                        ValueModuleResolution::Value(res) => Some(*res),
                        _ => None
                    })
                    .collect::<Vec<_>>();
                if results.is_empty() {
                    return Err(PathResolutionError::End(segments[0].span));
                }
                return Ok(results);
            }

            if results.is_empty() {
                if segments.len() == 1 {
                    return Err(PathResolutionError::End(segments[0].span));
                }
                let message = if let Some(prev) = prev {
                    Message::error(format!("cannot resolve type or module `{}` within `{}`", segments[0].ident.unwrap().symbol, prev.symbol))
                } else {
                    Message::error(format!("cannot resolve type or module `{}`", segments[0].ident.unwrap().symbol))
                };
                message
                    .at(segments[0].span)
                    .push(self.resolution.diagnostics);
                return Err(PathResolutionError::Emitted);
            }

            prev = segments[0].ident;
            segments = &segments[1..];
            in_local_space = false;
        }

        Err(PathResolutionError::Barrier)
    }

    fn resolve_path_in_space(&mut self, space: NameSpace, path: &'tcx ast::Path<'tcx>) {
        let span = match self.resolve_path(path) {
            Ok(results) => {
                if let Some(resolution) = results.select_priority(&[space]) {
                    path.segments.last().unwrap().resolve(resolution);
                    return;
                };
                path.segments.last().unwrap().span
            }
            Err(PathResolutionError::Emitted) => {
                path.segments.last().unwrap().resolve(Resolution::Err);
                return;
            }
            Err(PathResolutionError::Barrier) => return,
            Err(PathResolutionError::End(span)) => span, 
        };

        Message::error(format!("cannot find {space} `{name}`", name = path.segments.last().unwrap().ident.unwrap().symbol))
            .at(span)
            .push(self.resolution.diagnostics);
        path.segments.last().unwrap().resolve(Resolution::Err);
    }
 
    fn resolve_priority(&mut self, spaces: &[NameSpace], path: &'tcx ast::Path<'tcx>) {
        let span = match self.resolve_path(path) {
            Ok(results) => {
                if let Some(resolution) = results.select_priority(spaces) {
                    path.segments.last().unwrap().resolve(resolution);
                    return;
                };
                path.segments.last().unwrap().span
            }
            Err(PathResolutionError::Emitted) => {
                path.segments.last().unwrap().resolve(Resolution::Err);
                return;
            }
            Err(PathResolutionError::Barrier) => return,
            Err(PathResolutionError::End(span)) => span, 
        };

        Message::error(format!("cannot find {space} `{name}`", space = spaces[0], name = path.segments.last().unwrap().ident.unwrap().symbol))
            .at(span)
            .push(self.resolution.diagnostics);
        path.segments.last().unwrap().resolve(Resolution::Err);
    }
}

trait VMRsExt {
    fn get_module(&self) -> Option<Result<NodeId, ()>>;
    fn get_resolution(&self) -> Option<Resolution>;
}

impl VMRsExt for Vec<ValueModuleResolution> {
    fn get_module(&self) -> Option<Result<NodeId, ()>> {
        for res in self {
            match res {
                ValueModuleResolution::Module(module) => return Some(*module),
                _ => ()
            }
        }
        None
    }

    fn get_resolution(&self) -> Option<Resolution> {
        for res in self {
            match res {
                ValueModuleResolution::Value(resolution) => return Some(*resolution),
                _ => ()
            }
        }
        None
    }
}

trait ResolutionsExt {
    fn select_priority(self, spaces: &[NameSpace]) -> Option<Resolution>;
}

impl ResolutionsExt for Vec<Resolution> {
    fn select_priority(mut self, spaces: &[NameSpace]) -> Option<Resolution> {
        self.sort_by(|a, b| {
            let a = get_ns(a)
                .map(|a| spaces.iter().position(|p| a == *p))
                .flatten()
                .unwrap_or(usize::MAX);
            let b = get_ns(b)
                .map(|b| spaces.iter().position(|p| b == *p))
                .flatten()
                .unwrap_or(usize::MAX);

            a.cmp(&b)
        });

        fn get_ns(res: &Resolution) -> Option<NameSpace> {
            let ns = match res {
                Resolution::Local(_) => NameSpace::Variable,
                Resolution::Primitive(_) => NameSpace::Type,
                Resolution::Def(_, DefinitionKind::Enum | DefinitionKind::Struct | DefinitionKind::ParamTy | DefinitionKind::TypeAlias)
                    => NameSpace::Type,
                Resolution::Def(_, DefinitionKind::Const | DefinitionKind::Static | DefinitionKind::ParamConst)
                    => NameSpace::Variable,
                Resolution::Def(_, DefinitionKind::Function)
                    => NameSpace::Function,
                _ => return None,
            };
            return Some(ns);
        }

        let Some(first) = self.first() else {
            return None;
        };

        let Some(ns) = get_ns(&first) else {
            return None;
        };

        if !spaces.contains(&ns) {
            return None;
        }

        Some(*first)
    }
}

impl<'r, 'tcx> Visitor<'tcx> for NameResolutionPass<'r, 'tcx> {
    fn visit(&mut self, tree: &'tcx ast::SourceFile<'tcx>) {
        self.with_tfg_rigb(tree.node_id, |this| {
            node_visitor::visit_slice(tree.items, |item| this.visit_item(item));
        });
    }

    fn visit_item(&mut self, item: &'tcx ast::Item<'tcx>) {
        match &item.kind {
            ast::ItemKind::Function(function) => {
                self.with_tfg_rigb(item.node_id, |this| {
                    node_visitor::visit_slice(&function.sig.generics, |generic| this.visit_generic_param(generic));
                    this.visit_ty_expr(function.sig.returns);

                    let Some(ref body) = function.body else {
                        node_visitor::visit_slice(function.sig.params, |p| this.visit_param(p));
                        return;
                    };

                    this.with_rib(|this| {
                        node_visitor::visit_slice(function.sig.params, |p| this.visit_param(p));
                        this.visit_expr(body);
                    });
                })
            }
            ast::ItemKind::Struct(stc) => {
                self.with_tfg_rigb(item.node_id, |this| {
                    node_visitor::visit_slice(&stc.generics, |generic| this.visit_generic_param(generic));
                    node_visitor::visit_slice(stc.fields, |field_def| this.visit_field_def(field_def));
                    node_visitor::visit_slice(stc.items, |item| this.visit_item(item));
                });
                let def_id = *item.def_id.get().unwrap();
                let tfg_rib = &self.resolution.rib_map[&item.node_id];
                
                let definitions = std::iter::chain(tfg_rib.types.values(), tfg_rib.globals.values())
                    .filter_map(|decl| match decl.kind {
                        DefinitionKind::ParamTy | DefinitionKind::ParamConst => None,
                        _ => Some((decl.site, decl.kind))
                    })
                    .collect::<Vec<_>>();
                self.resolution.inner_items.insert(def_id, definitions);
            }
            ast::ItemKind::Enum(en) => {
                node_visitor::visit_option(en.representation, |repr| self.visit_ty_expr(repr));
                node_visitor::visit_slice(en.variants, |variant_def| self.visit_variant_def(variant_def));
            }
            ast::ItemKind::GlobalVar(global_var) => {
                node_visitor::visit_option(global_var.ty, |ty| self.visit_ty_expr(ty));
                node_visitor::visit_option(global_var.init, |expr| self.visit_expr(expr));
            }
            ast::ItemKind::Alias(alias) if let ast::AliasKind::Type(ty) = alias.kind => {
                self.with_tfg_rigb(item.node_id, |this| {
                    node_visitor::visit_slice(&alias.generics, |generic| this.visit_generic_param(generic));
                    this.visit_ty_expr(ty);
                });
            }, 
            ast::ItemKind::Alias(..) => (),
            ast::ItemKind::Import(..) => (), // import doesn't have relevance at this stage
            ast::ItemKind::Err => ()
        }
    }

    fn visit_field_def(&mut self, field_def: &'tcx ast::FieldDef<'tcx>) {
        if let Some(default_init) = &field_def.default_init {
            Message::fatal("struct default initalizers are not supported yet")
                .at(Span::new(default_init.span.start, field_def.span.end))
                .push(self.resolution.diagnostics);
        }
        self.visit_ty_expr(field_def.ty);
        node_visitor::visit_option(field_def.default_init, |default_init| self.visit_expr(default_init));
    }

    fn visit_stmt(&mut self, stmt: &'tcx ast::Stmt<'tcx>) {
        match &stmt.kind {
            ast::StmtKind::Local(local) => {
                node_visitor::visit_option(local.ty, |ret_ty| self.visit_ty_expr(ret_ty));
                node_visitor::visit_option(local.init, |init| self.visit_expr(init));

                self.define(local.ident, stmt.node_id);
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
                    this.enter_loop_ctxt(stmt.node_id, |this| this.visit_block(&while_loop.body));
                });
            }
            ast::StmtKind::For(for_loop) => {
                self.define(for_loop.bound_var, stmt.node_id);
                self.visit_expr(for_loop.iterator);
                self.with_rib(|this| {
                    this.enter_loop_ctxt(stmt.node_id, |this| this.visit_block(&for_loop.body));
                });
            }
            _ => node_visitor::noop_visit_stmt_kind(&stmt.kind, self),
        }
    }

    fn visit_control_flow(&mut self, control_flow: &'tcx ast::ControlFlow) {
        let Some(owner) = self.loop_owners.last() else {
            Message::error(format!("`{}` found outside of loop", control_flow.kind))
                .at(control_flow.span)
                .push(self.resolution.diagnostics);

            control_flow.destination.set(Err(OutsideScope)).unwrap();
            return;
        };
        control_flow.destination.set(Ok(*owner)).unwrap();
    }

    fn visit_path(&mut self, path: &'tcx ast::Path<'tcx>) {
        self.resolve_priority(&[NameSpace::Variable, NameSpace::Function], path);
    }

    fn visit_expr(&mut self, expr: &'tcx ast::Expr<'tcx>) {
        match &expr.kind {
            ast::ExprKind::Path(path) => self.visit_path(path),
            ast::ExprKind::TypeInit(ty_init) => {
                node_visitor::visit_slice(ty_init.initializers, |field| self.visit_type_init(field));
                match &ty_init.ty.kind {
                    ast::TypeExprKind::Path(path) => {
                        self.resolve_path_in_space(NameSpace::Type, path);
                    },
                    ast::TypeExprKind::Array(array) => {
                        self.visit_ty_expr(ty_init.ty);
                        match array.cap {
                            ast::ArrayCapacity::Discrete(ref expr) =>
                                self.visit_nested_const(expr),
                            ast::ArrayCapacity::Infer | ast::ArrayCapacity::Dynamic => ()
                        }
                    }
                    ast::TypeExprKind::Slice(ty) =>
                        self.visit_ty_expr(ty),
                    ast::TypeExprKind::Ref(..) =>
                        panic!("invalid state after parsing type init"),
                    ast::TypeExprKind::Err => ()
                }
            }
            ast::ExprKind::FunctionCall(call) if let ast::ExprKind::Path(path) = &call.callable.kind => {
                node_visitor::visit_slice(call.args, |arg| self.visit_argument(arg));
                self.resolve_priority(&[NameSpace::Function, NameSpace::Variable], path);
            }
            ast::ExprKind::Block(body) => {
                self.with_tfg_rigb(expr.node_id, |this| {
                    this.with_rib(|this| {
                        this.visit_block(body);
                    });
                });
            }
            ast::ExprKind::Field(field) =>
                self.visit_expr(field.expr),
            _ => node_visitor::noop_visit_expr_kind(&expr.kind, self)
        }
    }

    fn visit_param(&mut self, param: &'tcx ast::Param<'tcx>) {
        self.visit_ty_expr(&param.ty);

        if !self.has_rib() {
            return;
        }

        self.define(param.ident, param.node_id);
    }

    fn visit_ty_expr(&mut self, ty: &'tcx ast::TypeExpr<'tcx>) {
        match &ty.kind {
            ast::TypeExprKind::Ref(ty) => self.visit_ty_expr(ty),
            ast::TypeExprKind::Path(path) => {
                self.resolve_path_in_space(NameSpace::Type, path);
            },
            ast::TypeExprKind::Array(array) => {
                self.visit_ty_expr(array.ty);
                match array.cap {
                    ast::ArrayCapacity::Discrete(ref expr) =>
                        self.visit_nested_const(expr),
                    ast::ArrayCapacity::Infer | ast::ArrayCapacity::Dynamic => ()
                }
            }
            kind => node_visitor::noop_visit_ty_expr_kind(kind, self)
        }
    }
}

pub fn resolve_from_entry<'tcx>(
    session: &'tcx Session,
    entry: &'tcx ast::SourceFile<'tcx>,
    ast_info: &'tcx ast::AstInfo<'tcx>
) -> ResolutionResults<'tcx> {
    let mut resolution = ResolutionState::new(session, ast_info);

    let rpass = EarlyCollectionPass::new(&mut resolution);
    let modules = rpass.collect_bfs(entry, session, ast_info);

    let mut rpass = NameResolutionPass::new(&mut resolution);
    rpass.resolve(modules);

    resolution.results(entry.node_id)
}

pub struct ParentCollector {
    owner: ast::OwnerId,
    parent_stack: Vec<NodeId>,
    nodes: IndexVec<ast::LocalId, Option<NodeId>>
}

impl ParentCollector {
    fn new(owner: &ast::Owner) -> Self {
        let mut nodes = IndexVec::new();
        nodes.resize(owner.children.len(), None);

        Self {
            owner: owner.id,
            parent_stack: vec![],
            nodes
        }
    }

    fn record_and_parent(&mut self, node_id: NodeId, f: impl FnOnce(&mut Self)) {
        if node_id.owner == self.owner {
            self.nodes[node_id.local] = self.parent_stack.last().map(|x| *x);
        }
        self.parent_stack.push(node_id);
        f(self);
        self.parent_stack.pop();
    }

    fn as_map(self) -> ParentMap {
        ParentMap { nodes: self.nodes }
    }
}

impl<'tcx> Visitor<'tcx> for ParentCollector {
    fn visit(&mut self, tree: &'tcx ast::SourceFile<'tcx>) {
        self.record_and_parent(tree.node_id, |this| {
            node_visitor::noop_visit(tree, this);
        });
    }

    fn visit_item(&mut self, item: &'tcx ast::Item<'tcx>) {
        self.record_and_parent(item.node_id, |this| {
            if !matches!(item.kind, ast::ItemKind::Struct(..) | ast::ItemKind::Enum(..) | ast::ItemKind::Function(..)) || this.parent_stack.len() == 1 {
                node_visitor::noop_visit_item_kind(&item.kind, this);
            }
        });
    }
 
    fn visit_stmt(&mut self, stmt: &'tcx ast::Stmt<'tcx>) {
        self.record_and_parent(stmt.node_id, |this| {
            node_visitor::noop_visit_stmt_kind(&stmt.kind, this);
        });
    }

    fn visit_param(&mut self, param: &'tcx ast::Param<'tcx>) {
        self.record_and_parent(param.node_id, |this| {
            node_visitor::noop_visit_param(param, this);
        });
    }

    fn visit_expr(&mut self, expr: &'tcx ast::Expr<'tcx>) {
        self.record_and_parent(expr.node_id, |this| {
            node_visitor::noop_visit_expr_kind(&expr.kind, this);
        });
    }

    fn visit_generic_param(&mut self, param: &'tcx ast::GenericParam<'tcx>) {
        self.record_and_parent(param.node_id, |this| {
            node_visitor::noop_visit_generic_param_kind(&param.kind, this);
        });
    }

    fn visit_ty_expr(&mut self, ty: &'tcx ast::TypeExpr<'tcx>) {
        self.record_and_parent(ty.node_id, |this| {
            node_visitor::noop_visit_ty_expr_kind(&ty.kind, this);
        });
    }

    fn visit_field_def(&mut self, field_def: &'tcx ast::FieldDef<'tcx>) {
        self.record_and_parent(field_def.node_id, |this| {
            node_visitor::noop_visit_field_def(field_def, this);
        });
    }
    
    fn visit_variant_def(&mut self, variant_def: &'tcx ast::VariantDef<'tcx>) {
        self.record_and_parent(variant_def.node_id, |this| {
            node_visitor::noop_visit_variant_def(variant_def, this);
        });
    }

    fn visit_nested_const(&mut self, cnst: &'tcx ast::NestedConst<'tcx>) {
        self.record_and_parent(cnst.node_id, |this| {
            node_visitor::noop_visit_nested_const(cnst, this);
        });
    }
}

pub struct ParentMap {
    pub nodes: IndexVec<ast::LocalId, Option<NodeId>>
}

pub fn parent_map<'tcx>(tcx: TyCtxt<'tcx>, owner: ast::OwnerId) -> &'tcx ParentMap {
    let owners = tcx.resolutions.ast_info.global_owners.borrow(); 

    let owner = &owners[owner];
    let mut collector = ParentCollector::new(owner);
    match owner.node {
        ast::Node::Item(item) => collector.visit_item(item),
        ast::Node::SourceFile(source) => collector.visit(source),
        _ => unreachable!("cannot be owner node")
    }

    tcx.arena.alloc(collector.as_map())
}

