
use std::{collections::VecDeque, fmt::Write, io, path::{Path, PathBuf}, rc::Rc, str::FromStr};

use foldhash::quality::RandomState;
use hashbrown::{self, HashMap, hash_map::Entry};
use sha1::Digest;

use crate::{diagnostics::{DiagnosticsCtxt, Message}, files, session::Session, syntax::{ast::{self, DefinitionKind, IntoNode, NodeId, OutsideScope, Resolution}, lexer::Span, parser, symbol::{sym, Symbol}}};
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
            D::Struct | D::Enum => NameSpace::Type,
            D::Function => NameSpace::Function,
            D::Static | D::Const => NameSpace::Variable,
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

pub struct Definition {
    pub node: NodeId,
    pub kind: DefinitionKind
}

struct ResolutionState<'tcx> {
    items: Vec<ast::DefId>,
    file_cacher: Rc<files::FileCacher>,
    diagnostics: &'tcx DiagnosticsCtxt,
    rib_map: HashMap<NodeId, TFGRib>,
    node_to_path_map: HashMap<NodeId, PathBuf>,
    mangled_names: HashMap<NodeId, Symbol>,
    declarations: index_vec::IndexVec<ast::DefId, Definition>,
    ast_info: &'tcx ast::AstInfo<'tcx>,
}

pub struct ResolutionResults<'tcx> {
    pub ast_info: &'tcx ast::AstInfo<'tcx>,
    pub items: Vec<ast::DefId>,
    pub entry: Option<ast::DefId>,
    pub declarations: index_vec::IndexVec<ast::DefId, Definition>,
    pub node_to_path_map: HashMap<NodeId, PathBuf>,
    pub mangled_names: HashMap<NodeId, Symbol>,
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
#[derive(Default)]
struct TFGRib {
    types: HashMap<Symbol, Declaration>,
    functions: HashMap<Symbol, Declaration>,
    globals: HashMap<Symbol, Declaration>,
    modules: HashMap<Symbol, ModuleImport>,
    pending_imports: Vec<ModuleImport>,
}

impl TFGRib {
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
    ) {
        let declaration = Declaration {
            scope,
            site: resolution.declarations.push(Definition {
                node: site,
                kind
            }), 
            kind,
            span: name.span
        };
        resolution.items.push(declaration.site);
        self.define_with_declaration(name.symbol, declaration, resolution.diagnostics);
    }

    // FIXME: `define_with_declaration` and `define_aliased_module` share common code, so this
    // duplication should be removed 
    fn define_with_declaration(&mut self, symbol: Symbol, declaration: Declaration, diagnostics: &DiagnosticsCtxt) {
        let kind = declaration.kind;
        let space = match kind {
            DefinitionKind::Struct | DefinitionKind::Enum => &mut self.types,
            DefinitionKind::Function => &mut self.functions,
            DefinitionKind::Static | DefinitionKind::Const => &mut self.globals,
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
        let Ok(path) = path else {
            return;
        };

        let (file, _) = self.filemap.insert_full(path);
        let file = FileId::from_usize(file);

        let rib = self.ribs.last_mut().expect(".push_import neeeds to be called in valid TFGRib");
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

    fn define(&mut self, kind: DefinitionKind, name: ast::Ident, site: NodeId, scope: ast::Scope) {
        let rib = self.ribs.last_mut().expect(".define neeeds to be called in valid TFGRib");
        rib.define(kind, name, site, scope, self.resolution);
    }

    fn declare(&mut self, node: NodeId, kind: DefinitionKind) -> ast::DefId {
        self.resolution.declarations.push(Definition { node, kind })
    }

    fn with_rib<F: FnOnce(&mut Self)>(&mut self, node: NodeId, do_work: F) {
        self.ribs.push(TFGRib::default());
        do_work(self);
        let rib = self.ribs.pop().unwrap();
        if let Some(_) = self.resolution.rib_map.insert(node, rib) {
            panic!("tried to collect same rib twice {node:?}");
        }
    }
}

impl<'r, 'tcx> Visitor<'tcx> for EarlyCollectionPass<'r, 'tcx> {
    fn visit(&mut self, tree: &'tcx ast::SourceFile<'tcx>) {
        self.current_file.replace(tree);
        self.mangle_module_name(tree);
        self.with_rib(tree.node_id, |this| {
            node_visitor::visit_slice(tree.items, |item| this.visit_item(item));
        });
        self.current_file.take();
    }

    fn visit_item(&mut self, item: &'tcx ast::Item<'tcx>) {
        match &item.kind {
            ast::ItemKind::Struct(stc) => {
                self.define(DefinitionKind::Struct, stc.ident, item.node_id, item.scope);
                node_visitor::visit_slice(stc.fields, |field_def| self.visit_field_def(field_def));
                node_visitor::visit_slice(stc.generics, |generic| self.visit_generic_param(generic));
            }, 
            ast::ItemKind::Enum(en) => {
                self.define(DefinitionKind::Enum, en.ident, item.node_id, item.scope);
                node_visitor::visit_slice(en.variants, |variant_def| self.visit_variant_def(variant_def));
            },
            ast::ItemKind::Function(function) => {
                self.define(DefinitionKind::Function, function.ident, item.node_id, item.scope);
                node_visitor::visit_fn(function, self);
            },
            ast::ItemKind::GlobalVar(global) => {
                self.define(
                    if global.constant {DefinitionKind::Const} else {DefinitionKind::Static},
                    global.ident, item.node_id, item.scope);
                node_visitor::visit_option(global.ty, |ty| self.visit_ty_expr(ty));
                node_visitor::visit_option(global.init, |expr| self.visit_expr(expr));
            }
            ast::ItemKind::Import(import) => {
                let file = self.current_file.expect("visit_import should be operating within source file");
                self.push_import(file, &import.path, None, item.span);
            }
            ast::ItemKind::Alias(alias) => {
                let ast::ItemKind::Import(import) = alias.item.kind else {
                    unreachable!("non-import aliases are currently unsupported");
                };
                let file = self.current_file.expect("visit_import should be operating within source file");
                self.push_import(file, &import.path, Some(alias.ident.symbol), item.span);
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
        node_visitor::visit_option(variant_def.sset, |sset| self.visit_nested_const(sset));
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

    fn with_tbg_rib<F: FnOnce(&mut Self)>(&mut self, node: NodeId, do_work: F) {
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

    fn resolve_path_in_space(&self, space: NameSpace, path: &ast::Path, report_error: bool) -> bool {
        todo!("path resolving is a novel problem")
        /*if name.resolution().is_some() {
            return true;
        }
        let rib = *self.tfg_ribs.last().expect(".resolve() called without valid TFGRib");
        let rib = &self.resolution.rib_map[&rib];
        let decl = match space {
            NameSpace::Type => rib.types.get(&name.ident.symbol),
            NameSpace::Function => rib.functions.get(&name.ident.symbol),
            NameSpace::Variable => rib.globals.get(&name.ident.symbol)
        };
        if let Some(local) = self.resolve_local(name.ident.symbol) {
            name.resolve(Resolution::Local(local.site));
        } else if let Some(decl) = decl {
            name.resolve(Resolution::Def(decl.site, decl.kind));
        } else if name.ident.symbol.is_primitive_ty() && space == NameSpace::Type {
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
        true*/
    }

    fn resolve_priority(&self, pspaces: &[NameSpace], path: &ast::Path) -> bool {
        for space in pspaces {
            if self.resolve_path_in_space(*space, path, false) {
                return true;
            }
        }
        let name: ast::Ident = todo!("find the first ill-resolved segment of this path");
        Message::error(format!("could not find {space} {name}", space = pspaces[0], name = name.symbol))
            .at(path.span)
            .push(self.resolution.diagnostics);
        path.resolve(Resolution::Err);
        false
    }
}

impl<'r, 'tcx> Visitor<'tcx> for NameResolutionPass<'r, 'tcx> {
    fn visit(&mut self, tree: &'tcx ast::SourceFile<'tcx>) {
        self.with_tbg_rib(tree.node_id, |this| {
            node_visitor::visit_slice(tree.items, |item| this.visit_item(item));
        });
    }

    fn visit_item(&mut self, item: &'tcx ast::Item<'tcx>) {
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
                node_visitor::visit_option(global_var.ty, |ty| self.visit_ty_expr(ty));
                node_visitor::visit_option(global_var.init, |expr| self.visit_expr(expr));
            }
            ast::ItemKind::Import(..) => (), // import doesn't have relevance at this stage
            ast::ItemKind::Alias(alias) => todo!(),
            ast::ItemKind::Err => ()
        }
    }

    fn visit_variant_def(&mut self, variant_def: &'tcx ast::VariantDef<'tcx>) {
        if let Some(sset) = &variant_def.sset {
            Message::fatal("setting explicit enum tag values is not supported yet")
                .at(Span::new(sset.span.start, sset.span.end))
                .push(self.resolution.diagnostics);
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
                        self.resolve_path_in_space(NameSpace::Type, path, true);
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
                self.with_rib(|this| {
                    this.visit_block(body);
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
                self.resolve_path_in_space(NameSpace::Type, path, true);
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

