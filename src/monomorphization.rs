
// use inkwell::module::Linkage;

use std::collections::VecDeque;

use hashbrown::{HashMap, hash_map::Entry};

use crate::{analysis::intermediate::{self, Body}, context::TyCtxt, layout, syntax::{ast, symbol::Symbol}, type_ir::{ Const, GenericArgs, Instatiatable}};

pub struct CodegenUnit<'tcx> {
    pub items: Vec<Item<'tcx>>,
    pub mangled_name: Symbol,
    pub source_file_name: String,
}

impl<'tcx> CodegenUnit<'tcx> {
    fn push(&mut self, item: Item<'tcx>) {
        self.items.push(item);
    }
}

pub struct Item<'tcx> {
    pub kind: ItemKind<'tcx>,
    pub name: Symbol,
    pub mangeled_name: Symbol,
    // pub linkage: Linkage
}

pub enum ItemKind<'tcx> {
    Function(&'tcx Body<'tcx>),
    Global(Const<'tcx>),
}

pub struct Mangler<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> Mangler<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx }
    }

    fn mangle_item_name(
        &mut self,
        item: &'tcx ast::Item<'tcx>,
        generic_args: &'tcx GenericArgs<'tcx>
    ) -> Symbol {
        todo!()
    }

    fn mangle_module_name(
        &mut self,
        module: &'tcx ast::SourceFile<'tcx>
    ) -> Symbol {
        todo!()
    }
}

pub struct Collector<'tcx> {
    tcx: TyCtxt<'tcx>,
    depedency_queue: VecDeque<DependencyKind<'tcx>>,
    units: HashMap<ast::NodeId, CodegenUnit<'tcx>>,
    mangler: Mangler<'tcx>
}

#[derive(Clone, Copy)]
enum DependencyKind<'tcx> {
    Function(ast::DefId, &'tcx GenericArgs<'tcx>),
    Global(ast::DefId, Const<'tcx>),
}

impl<'tcx> DependencyKind<'tcx> {
    fn def(self) -> ast::DefId {
        match self {
            DependencyKind::Function(def, _) => def,
            DependencyKind::Global(def, _) => def,
        }
    }
}

impl<'tcx> Collector<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            depedency_queue: Default::default(),
            units: Default::default(),
            mangler: Mangler::new(tcx)
        }
    }

    fn collect_place(&mut self, place: &'tcx intermediate::Place<'tcx>) {
        for translation in place.translation_chain {
            if let intermediate::PtrTranslation::Index { idx } = translation {
                self.collect_operand(idx);
            }
        }
    }

    fn handle_const(&mut self, _cnst: layout::Const<'tcx>) {
        todo!()
    }

    fn collect_operand(&mut self, operand: &'tcx intermediate::Operand<'tcx>) {
        if let intermediate::Operand::Const(cnst) = operand {
            self.handle_const(*cnst);
        }
    }

    fn collect_in_statement(&mut self, statement: &'tcx intermediate::Statement<'tcx>) {
        if let Some(place) = &statement.place {
            self.collect_place(place);
        }
        match &statement.rhs {
            intermediate::RValue::Ref(place) | intermediate::RValue::Read(place) =>
                self.collect_place(place),
            intermediate::RValue::Invert(operand) | intermediate::RValue::Negate(operand) |
            intermediate::RValue::Cast { value: operand, .. }=>
                self.collect_operand(operand),
            intermediate::RValue::Const(cnst) =>
                self.handle_const(*cnst),
            intermediate::RValue::BinaryOp { lhs, rhs, .. } => {
                self.collect_operand(lhs);
                self.collect_operand(rhs);
            }
            intermediate::RValue::Call { callee, args } => {
                self.collect_operand(callee);
                for arg in args {
                    self.collect_operand(&arg.operand);
                }
            }
            intermediate::RValue::ExplicitInit { initializers, .. } => {
                for (_, init) in initializers {
                    self.collect_operand(&init.operand);
                }
            }
        }
    }

    fn collect_in_terminator(&mut self, terminator: &'tcx intermediate::Terminator<'tcx>) {
        match &terminator.kind {
            intermediate::TerminatorKind::Diverge { condition, .. } => 
                self.collect_operand(condition),
            intermediate::TerminatorKind::Return { value: Some(value) } =>
                self.collect_operand(value),
            _ => (),
        }
    }

    fn collect_in_block(&mut self, block: &'tcx intermediate::BasicBlock<'tcx>) {
        for statement in &block.statements {
            self.collect_in_statement(statement);
        }
        self.collect_in_terminator(block.terminator.get().unwrap());
    }

    fn collect_in_body(&mut self, body: &'tcx Body<'tcx>) {
        for block in &body.basic_blocks {
            self.collect_in_block(block);
        }
    }

    fn collect(mut self) -> Vec<CodegenUnit<'tcx>> {
        while let Some(dependency) = self.depedency_queue.pop_front() {
            let element = dependency.def();
            let ast::Node::Item(item) = self.tcx.node_by_def_id(element) else {
                unreachable!("dependency needs to be an Node::Item")
            };

            let module = get_module_for_def(self.tcx, element);

            let mut generic_args: &'tcx GenericArgs<'tcx> = GenericArgs::empty();
            let kind = match dependency {
                DependencyKind::Function(_, generics) => {
                    let body = self.tcx.build_ir(element)
                        .expect("valid body should exist for mono item");
                    let body = self.tcx.instantiate_body((body, generics));

                    self.collect_in_body(body);

                    generic_args = generics;
                    ItemKind::Function(body)
                }
                DependencyKind::Global(_, initializer) => ItemKind::Global(initializer)
            };

            let cgu = match self.units.entry(module.node_id) {
                Entry::Occupied(entry) => entry.into_mut(),
                Entry::Vacant(entry) => {
                    let path = &self.tcx.resolutions.node_to_path_map[&module.node_id];
                    let file_name = path.file_name().unwrap();
                    let source_file_name = std::str::from_utf8(file_name.as_encoded_bytes())
                        .unwrap()
                        .to_string();

                    let mangled_name = self.mangler.mangle_module_name(module);

                    entry.insert(CodegenUnit {
                        items: Vec::new(),
                        mangled_name,
                        source_file_name
                    })
                },
            };

            cgu.push(Item {
                kind,
                name: item.ident().symbol,
                mangeled_name: self.mangler.mangle_item_name(item, generic_args)
            });
        }
        todo!()
    }
}

fn get_module_for_def<'tcx>(tcx: TyCtxt<'tcx>, def: ast::DefId) -> &'tcx ast::SourceFile<'tcx> {
    let mut node = tcx.node_by_def_id(def);
    let owners = tcx.resolutions.ast_info.global_owners.borrow();
    loop {
        if let ast::Node::SourceFile(module) = node {
            return module;
        }
        node = owners[node.node_id().owner].node;
    }
}

pub fn monomorph_items<'tcx>(tcx: TyCtxt<'tcx>) -> Vec<CodegenUnit<'tcx>> {
    let mut collector = Collector::new(tcx);

    // FIXME: for both entry and any `#c_call` fns, no generic params need to be ensured
    let entry = tcx.resolutions.entry.expect("program should have an entrypoint");
    collector.depedency_queue.push_back(DependencyKind::Function(entry, GenericArgs::empty()));

    for &def in &tcx.resolutions.items {
        let node = tcx.node_by_def_id(def);
        if let ast::Node::Item(ast::Item { kind: ast::ItemKind::Function(func), .. }) = node && func.sig.header.c_call.is_some() {
            collector.depedency_queue.push_back(DependencyKind::Function(def, GenericArgs::empty()));
        }
    }

    collector.collect()
}

pub fn instantiate_body<'tcx>(tcx: TyCtxt<'tcx>, key: (&'tcx Body<'tcx>, &'tcx GenericArgs<'tcx>)) -> &'tcx Body<'tcx> {
    let (body, generics) = key; 
    let body = body
        .clone()
        .instantiate(generics, tcx);
    tcx.arena.alloc(body)
}

