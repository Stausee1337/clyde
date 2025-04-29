use std::{cell::RefCell, collections::VecDeque};

use index_vec::IndexVec;
use ll::BasicType;
use hashbrown::{HashMap, hash_map::Entry};

use crate::{analysis::intermediate, context::TyCtxt, syntax::ast, target::{DataLayoutExt, TargetDataLayout}, type_ir::{self, AdtDef, AdtKind, Ty, TyKind, TypeLayout}};

struct CodeBuilder<'a, 'll, 'tcx> {
    module: &'ll ll::Module<'ll>,
    builder: ll::Builder<'ll>,
    function: ll::FunctionValue<'ll>,
    generator: &'a mut CodegenCtxt<'ll, 'tcx>,
    block_translations: IndexVec<intermediate::BlockId, Option<ll::BasicBlock<'ll>>>
}

impl<'a, 'll, 'tcx> CodeBuilder<'a, 'll, 'tcx> {
    fn new(
        module: &'ll ll::Module<'ll>,
        function: ll::FunctionValue<'ll>,
        generator: &'a mut CodegenCtxt<'ll, 'tcx>
    ) -> Self {
        let builder = module.get_context().create_builder();
        Self {
            module,
            builder,
            function,
            generator,
            block_translations: IndexVec::new()
        }
    }

    fn visit_statement(&mut self, _statement: &'tcx intermediate::Statement<'tcx>) {

    }

    fn visit_terminator(&mut self, _terminator: &'tcx intermediate::Terminator<'tcx>) {

    }

    fn visit_basic_block(&mut self, block: &'tcx intermediate::BasicBlock<'tcx>) {
        for statement in &block.statements {
            self.visit_statement(statement);
        }
        let terminator = block.terminator
            .get()
            .expect("every IR block should be terminated");
        self.visit_terminator(terminator);
    }

    fn visit_body(&mut self, body: &'tcx intermediate::Body<'tcx>) {
        for (id, block) in body.basic_blocks.iter_enumerated() {
            let basic_block = self.resolve_block(id);
            self.builder.position_at_end(basic_block);
            self.visit_basic_block(block);
        }
    }

    fn resolve_block(&mut self, block_id: intermediate::BlockId) -> ll::BasicBlock<'ll> {
        if let Some(block) = self.block_translations.get(block_id).map(|x| *x).flatten() {
            return block;
        }
        if self.block_translations.len_idx() <= block_id {
            self.block_translations.resize(block_id.index() + 1, None);
        }
        let context = self.module.get_context();
        let block = context.append_basic_block(self.function, "");
        self.block_translations[block_id] = Some(block);
        block
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum DependencyState {
    Pending, Done
}

struct DependencyData<'ll> {
    value: ll::FunctionValue<'ll>,
    state: DependencyState
}

struct CodegenCtxt<'ll, 'tcx> {
    tcx: TyCtxt<'tcx>,
    // FIXME: this should be a TypedArena, as this way we won't leak all the `ll::Context`s and
    // thier associated modules and can properly regain ownership
    arena: &'ll bumpalo::Bump,
    context: &'ll ll::Context,
    module_map: HashMap<ast::NodeId, &'ll ll::Module<'ll>>,
    dependency_map: HashMap<ast::DefId, DependencyData<'ll>>,
    type_translation_cache: RefCell<HashMap<Ty<'tcx>, ll::AnyTypeEnum<'ll>>>,
    depedency_queue: VecDeque<ast::DefId>,
    target_data_layout: TargetDataLayout
}

impl<'ll, 'tcx> CodegenCtxt<'ll, 'tcx> {
    fn new(tcx: TyCtxt<'tcx>, arena: &'ll bumpalo::Bump) -> Self {
        let context = arena.alloc(ll::Context::create());
        Self {
            tcx,
            arena,
            context,
            module_map: HashMap::new(),
            dependency_map: HashMap::new(),
            type_translation_cache: RefCell::new(HashMap::new()),
            depedency_queue: VecDeque::new(),
            target_data_layout: *tcx.data_layout()
        }
    }

    fn push_dependency(&mut self, def: ast::DefId) -> ll::FunctionValue<'ll> {
        if let Some(DependencyData { value, .. }) = self.dependency_map.get(&def) {
            return *value;
        }

        let node = self.tcx.node_by_def_id(def);
        let ast::Node::Item(item @ ast::Item { kind: ast::ItemKind::Function(..), .. }) = node else {
            panic!("CodegenCtxt::push_dependency is exclusive to functions");
        };

        let state = if let Some(..) = node.body() {
            self.depedency_queue.push_back(def);
            DependencyState::Pending
        } else {
            DependencyState::Done
        };

        let module = self.get_module_for_def(def);
        let ty = self.tcx.type_of(def);

        let function = module
            .add_function(
                item.ident().symbol.get(),
                ty.llvm_type(self).into_function_type(),
                Some(ll::Linkage::External)
            );
        let data = DependencyData {
            value: function, state
        };
        self.dependency_map.insert(def, data);
        function
    }

    fn generate_code_bfs(&mut self) {
        while let Some(element) = self.depedency_queue.pop_front() {
            let value = self.dependency_map[&element].value;
            let module = self.get_module_for_def(element);

            let body = self.tcx.build_ir(element)
                .expect("valid body should exist for codegen item");

            let mut builder = CodeBuilder::new(module, value, self);
            builder.visit_body(body);

            self.dependency_map.get_mut(&element)
                .unwrap()
                .state = DependencyState::Done;
        }
    }

    fn get_module_for_def(&mut self, def: ast::DefId) -> &'ll ll::Module<'ll> {
        let mut node = self.tcx.node_by_def_id(def);
        {
            let owners = self.tcx.resolutions.ast_info.global_owners.borrow();
            loop {
                if let ast::Node::SourceFile(..) = node {
                    break;
                }
                node = owners[node.node_id().owner].node;
            }
        }
        match self.module_map.entry(node.node_id()) {
            Entry::Vacant(entry) => {
                let module = Self::create_module(node, self.context, self.arena);
                entry.insert(module)
            }
            Entry::Occupied(entry) => entry.into_mut()
        }
    }

    fn create_module(node: ast::Node<'tcx>, context: &'ll ll::Context, arena: &'ll bumpalo::Bump) -> &'ll ll::Module<'ll> {
        let ast::Node::SourceFile(module) = node else {
            panic!("non source-level module in CodegenCtxt::create_module");
        };
        Self::create_module_by_name(module.name.get(), context, arena)
    }

    fn create_module_by_name(name: &str, context: &'ll ll::Context, arena: &'ll bumpalo::Bump) -> &'ll ll::Module<'ll> {
        arena.alloc(context.create_module(name))
    }
}

impl<'ll, 'tcx> DataLayoutExt for CodegenCtxt<'ll, 'tcx> {
    fn data_layout(&self) -> &TargetDataLayout {
        &self.target_data_layout
    }
}

impl<'tcx> Ty<'tcx> {
    fn llvm_type<'ll>(&self, ctxt: &CodegenCtxt<'ll, 'tcx>) -> ll::AnyTypeEnum<'ll> {
        if let Some(cached) = ctxt.type_translation_cache.borrow().get(self) {
            return *cached;
        }

        let layout = ctxt.tcx.layout_of(*self)
            .ok()
            .expect("Ty should have valid layout at codegen stage");

        let ll_type = llvm_lower_type_and_layout(*self, layout, ctxt);
        ctxt.type_translation_cache.borrow_mut().insert(*self, ll_type);

        ll_type
    }
}

fn llvm_lower_type_and_layout<'ll, 'tcx>(ty: Ty<'tcx>, layout: TypeLayout<'tcx>, ctxt: &CodegenCtxt<'ll, 'tcx>) -> ll::AnyTypeEnum<'ll> {
    if let type_ir::BackendRepr::Scalar(scalar) = layout.repr {
        return llvm_lower_scalar(scalar, ctxt);
    }

    match ty {
        // TODO: is never == void ok here?
        Ty(TyKind::Void | TyKind::Never) => 
            return ll::AnyTypeEnum::VoidType(ctxt.context.void_type()),
        Ty(TyKind::Function(def)) => {
            let signature = ctxt.tcx.fn_sig(*def);
            let ret_ty = signature.returns.llvm_type(ctxt);
            let mut param_tys = Vec::<ll::BasicMetadataTypeEnum<'ll>>::with_capacity(signature.params.len());
            for param in signature.params {
                param_tys.push(param.ty.llvm_type(ctxt).try_into().unwrap());
            }
            let ret_ty: ll::BasicTypeEnum<'ll> = ret_ty.try_into().unwrap();
            return ll::AnyTypeEnum::FunctionType(ret_ty.fn_type(&param_tys, false));
        }
        Ty(TyKind::Int(..) | TyKind::Float(..) | TyKind::Char | TyKind::Bool) =>
            panic!("should have been picked up by BackendRepr::Scalar and been handled"),
        Ty(TyKind::Err) => panic!("there it should be no error types in codegen pass"),
        _ => ()
    }

    match layout.fields {
        type_ir::Fields::Scalar => unreachable!(),
        type_ir::Fields::Array { count, .. } => {
            let base_ty: ll::BasicTypeEnum<'ll> = ty.llvm_type(ctxt).try_into().unwrap();
            ll::AnyTypeEnum::ArrayType(base_ty.array_type(count as u32))
        }
        type_ir::Fields::Struct { ref fields } =>
            llvm_lower_fields(ty, fields.iter_enumerated().map(|(f, o)| (f, *o)), ctxt)
    }
}

fn llvm_lower_scalar<'ll, 'tcx>(scalar: type_ir::Scalar, ctxt: &CodegenCtxt<'ll, 'tcx>) -> ll::AnyTypeEnum<'ll> {
    let context = ctxt.context;
    match scalar {
        type_ir::Scalar::Int(int, _) => {
            let int_type = match int {
                type_ir::Integer::I8 => context.i8_type(),
                type_ir::Integer::I16 => context.i16_type(),
                type_ir::Integer::I32 => context.i32_type(),
                type_ir::Integer::I64 => context.i64_type(),
                type_ir::Integer::ISize => {
                    let normalized = type_ir::Scalar::Int(int.normalize(ctxt), false);
                    return llvm_lower_scalar(normalized, ctxt);
                }
            };
            ll::AnyTypeEnum::IntType(int_type)
        }
        type_ir::Scalar::Float(float) => {
            let float_type = match float {
                type_ir::Float::F32 => context.f32_type(),
                type_ir::Float::F64 => context.f64_type(),
            };
            ll::AnyTypeEnum::FloatType(float_type)
        }
        type_ir::Scalar::Pointer =>
            ll::AnyTypeEnum::PointerType(context.ptr_type(ll::AddressSpace::from(0)))
    }

}

fn llvm_lower_fields<'ll, 'tcx>(ty: Ty<'tcx>, _field_offsets: impl Iterator<Item = (type_ir::FieldIdx, u64)>, ctxt: &CodegenCtxt<'ll, 'tcx>) -> ll::AnyTypeEnum<'ll> {
    let name;
    let field_tys = match ty {
        Ty(TyKind::String | TyKind::Slice(..)) => {
            name = None;
            let nuint = llvm_lower_scalar(
                type_ir::Scalar::Int(type_ir::Integer::ISize.normalize(ctxt), false),
                ctxt)
                .try_into()
                .unwrap();

            let mut fields = vec![];
            fields.push(ll::BasicTypeEnum::PointerType(ctxt.context.ptr_type(ll::AddressSpace::from(0)))); // void *data;
            fields.push(nuint);                                                                          // nuint count;
            fields
        }
        Ty(TyKind::DynamicArray(..)) => {
            name = None;
            let nuint = llvm_lower_scalar(
                type_ir::Scalar::Int(type_ir::Integer::ISize.normalize(ctxt), false),
                ctxt)
                .try_into()
                .unwrap();

            let mut fields = vec![];
            fields.push(ll::BasicTypeEnum::PointerType(ctxt.context.ptr_type(ll::AddressSpace::from(0)))); // void *items;
            fields.push(nuint);                                                                          // nuint count;
            fields.push(nuint);                                                                          // nuint capacity;
            fields
        }
        Ty(TyKind::Adt(AdtDef(AdtKind::Struct(strct)))) => {
            name = Some(strct.name);
            strct.fields()
                .map(|(_, data)| {
                    let ty = ctxt.tcx.type_of(data.def);
                    ty.llvm_type(ctxt).try_into().expect("struct fields should be LLVM BasicTypes")
                })
                .collect::<Vec<_>>()
        }
        Ty(TyKind::Adt(AdtDef(AdtKind::Union))) => todo!(),
        Ty(TyKind::Range(..)) => todo!(),
        else_ => panic!("{else_:?} is invalid here")
    };

    // TODO(once CSE and non-C structs are available): add padding fields to accomplish the
    // calculated offsets. For now they should be equal

    let strct;
    if let Some(name) = name {
        strct = ctxt.context.opaque_struct_type(name.get());
        strct.set_body(&field_tys, false);
    } else {
        strct = ctxt.context.struct_type(&field_tys, false);
    }

    ll::AnyTypeEnum::StructType(strct)
}

pub struct CodegenResults;

pub fn run_codegen(tcx: TyCtxt) -> CodegenResults {
    let arena = bumpalo::Bump::new();

    let entry = tcx.resolutions.entry.expect("program should have an entrypoint");

    let mut ctxt = CodegenCtxt::new(tcx, &arena);
    let entry = ctxt.push_dependency(entry);

    ctxt.generate_code_bfs();
    todo!()
}

mod ll {
    pub use inkwell::{
        context::Context,
        module::{Module, Linkage},
        builder::Builder,
        basic_block::BasicBlock,
        types::{FunctionType, AnyTypeEnum, BasicTypeEnum, BasicMetadataTypeEnum, BasicType},
        values::FunctionValue,
        AddressSpace
    };
}

