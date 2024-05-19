
use std::{collections::HashMap, ops::Range};

use crate::{ast, node_visitor::{MutVisitor, self}, diagnostics::{Diagnostics, self}, symbol::Symbol};

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
        write!(f, "Hello")
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
                .error(format!("Redeclartion of {space_kind} {name:?}", name = name.symbol.get()))
                .with_span(name.span);
            self.diagnostics
                .note(format!("Previous declaration of {name:?} here", name = name.symbol.get()))
                .with_pos(prev.span.start);
        }
    }
}

struct TypeResolutionPass<'r> {
    resolution: &'r mut ResolutionState
}

impl<'r> TypeResolutionPass<'r> {
    pub fn new(resolution: &'r mut ResolutionState) -> Self {
        Self { resolution }
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
}


pub fn run_resolve(tree: &mut ast::TopLevel) {
    let mut resolution = ResolutionState::new(tree.diagnostics);

    let mut rpass = TypeResolutionPass::new(&mut resolution);
    rpass.visit(tree);
}

