use std::{cell::RefCell, collections::VecDeque, ffi::OsString, fmt::Write, process::Command};

use index_vec::IndexVec;
use ll::{BasicType, BasicValue};
use hashbrown::{HashMap, HashSet, hash_map::Entry};

use crate::{analysis::intermediate::{self, Mutability, RegisterId}, context::{ModuleInfo, TyCtxt}, layout::{self, Scalar, TyLayoutTuple}, monomorphization, session::OptimizationLevel, syntax::{ast, symbol::{self, sym}}, target::{DataLayoutExt, TargetDataLayout}, type_ir::{self, AdtDef, AdtKind, Instatiatable, Ty, TyKind}};
use clyde_macros::base_case_handler;

macro_rules! ensure {
    ($expr:expr) => {
        match $expr {
            Ok(ok) => ok,
            Err(err) => {
                panic!("Bug: ll::Builder failed with error: {err:?}");
            }
        }
    };
}

#[derive(Debug, Clone, Copy)]
struct Place<'ll> {
     value: ll::PointerValue<'ll>,
     align: layout::Align,
}

#[derive(Debug, Clone, Copy)]
enum ValueKind<'ll> {
    /// represents a value that MUST not fit into a usual llvm immediate, but has to be
    /// represented by a place to a stack pointer. i.e. BackendRepr must be Memory
    Ref(Place<'ll>),
    /// represents a value that MUST always fit into an llvm immediate
    /// i.e. BackendRepr must be Scalar
    Immediate(ll::BasicValueEnum<'ll>),
    /// represents a value that MUST always fit into two llvm immediates
    /// i.e. BackendRepr must be ScalarPair
    Pair(ll::BasicValueEnum<'ll>, ll::BasicValueEnum<'ll>),
}

#[derive(Debug, Clone, Copy)]
struct Value<'ll, 'tcx> {
    kind: ValueKind<'ll>,
    layout: TyLayoutTuple<'tcx>
}

impl<'ll, 'tcx> Value<'ll, 'tcx> {
    fn deref<'a>(&self, builder: &mut CodeBuilder<'a, 'll, 'tcx>) -> (Place<'ll>, TyLayoutTuple<'tcx>){
        match self.kind {
            ValueKind::Immediate(value) => {
                let Ty(TyKind::Refrence(inner)) = self.layout.ty else {
                    panic!("Cannot deref {:?}", self.layout);
                };
                let place = Place {
                    value: value.into_pointer_value(),
                    align: self.layout.align
                };
                (place, builder.cctxt.tcx.layout_of(*inner).unwrap())
            }
            ValueKind::Pair(value1, _) => {
                let inner = match self.layout.ty {
                    // HACK: make string and slice trivially derefrencable to thier containted
                    // types
                    Ty(TyKind::String) => builder.tcx.basic_types.byte,
                    Ty(TyKind::Slice(el)) => *el,
                    _ => panic!("cannot deref ValueKimd::Pair: pointers always fit into immediates")
                };
                let data_layout = builder.cctxt.data_layout();
                let place = Place {
                    value: value1.into_pointer_value(),
                    align: data_layout.ptr_align
                };
                (place, builder.cctxt.tcx.layout_of(inner).unwrap())
            }
            ValueKind::Ref(..) =>
                panic!("cannot deref ValueKind::Ref:  pointers always fit into immediates")
        }
    }

    fn store<'a>(&self, 
        dest: Place<'ll>,
        _layout: TyLayoutTuple<'tcx>,
        builder: &mut CodeBuilder<'a, 'll, 'tcx>
    ) {
        debug_assert_eq!(_layout, self.layout, "why shouldn't that be the case?");
        match self.kind {
            ValueKind::Immediate(value) => {
                let value: ll::BasicValueEnum<'ll> = value.force_into();
                let instruction = ensure!(builder.builder.build_store(dest.value, value));
                instruction.set_alignment(dest.align.in_bytes() as u32)
                    .unwrap();
            }
            ValueKind::Pair(value1, value2) => {
                let value1: ll::BasicValueEnum<'ll> = value1.force_into();
                let value2: ll::BasicValueEnum<'ll> = value2.force_into();

                let mut ptr = dest.value;

                let layout::BackendRepr::ScalarPair(scalar1, scalar2) = self.layout.repr else {
                    panic!("ValueKind should match BackendRepr");
                };

                let instruction = ensure!(builder.builder.build_store(ptr, value1));
                instruction.set_alignment(dest.align.in_bytes() as u32)
                    .unwrap();


                let align = scalar2.align(builder.cctxt);
                let offset = scalar1.size(builder.cctxt).align_up(align);
                let offset = builder.cctxt.context.i32_type().const_int(offset, false);

                ptr = unsafe { 
                    ensure!(builder.builder.build_in_bounds_gep(
                        builder.cctxt.context.i8_type(),
                        ptr,
                        &[offset],
                        ""
                    ))
                };

                let instruction = ensure!(builder.builder.build_store(ptr, value2));
                instruction.set_alignment(dest.align.in_bytes() as u32)
                    .unwrap();
            }
            ValueKind::Ref(place) => {
                // TODO: only load-store when opt_level == OptLevel::None
                // TODO: add llvm metadata
                if self.layout.is_llvm_immediate() {
                    let value = builder.load_value(place, self.layout);
                    value.store(dest, self.layout, builder);
                } else if self.layout.size.in_bytes > 0 {
                    let llvm_i64 = builder.cctxt.context.i64_type();
                    ensure!(builder.builder.build_memcpy(
                        dest.value, dest.align.in_bytes() as u32,
                        place.value, place.align.in_bytes() as u32,
                        llvm_i64.const_int(self.layout.size.in_bytes, false)));
                }
            }
        }
    }
}

#[derive(Default, Clone, Copy)]
enum LocalKind<'ll, 'tcx> {
     Value(Value<'ll, 'tcx>),
     Place {
         place: Place<'ll>,
         layout: TyLayoutTuple<'tcx>
     },
     #[default]
     Dangling
}

enum DeferredStorage<'ll, 'tcx> {
    Place {
         place: Place<'ll>,
         layout: TyLayoutTuple<'tcx>, 
    },
    Initialize(intermediate::RegisterId),
    None,
}

impl<'ll, 'tcx> DeferredStorage<'ll, 'tcx> {
    fn store_or_init<'a>(self, value: Value<'ll, 'tcx>, builder: &mut CodeBuilder<'a, 'll, 'tcx>) {
        match self {
            DeferredStorage::Place { place, layout: ty } =>
                value.store(place, ty, builder),
            DeferredStorage::Initialize(reg) => {
                let local = &mut builder.reg_translations[reg];
                assert!(matches!(local, LocalKind::Dangling));
                *local = LocalKind::Value(value);
            }
            DeferredStorage::None => ()
        }
    }

    fn dissolve(self) -> (Option<(Place<'ll>, TyLayoutTuple<'tcx>)>, Option<Self>) {
        match self {
            DeferredStorage::Place { place, layout: ty } => (Some((place, ty)), None),
            DeferredStorage::None | DeferredStorage::Initialize(..) => (None, Some(self)), 
        }
    }
}

struct CodeBuilder<'a, 'll, 'tcx> {
    tcx: TyCtxt<'tcx>,
    cctxt: &'a mut CodegenCtxt<'ll, 'tcx>,
    module: &'ll ll::Module<'ll>,
    builder: ll::Builder<'ll>,
    function: ll::FunctionValue<'ll>,
    reg_translations: IndexVec<intermediate::RegisterId, LocalKind<'ll, 'tcx>>,
    block_translations: IndexVec<intermediate::BlockId, Option<ll::BasicBlock<'ll>>>
}

impl<'a, 'll, 'tcx> CodeBuilder<'a, 'll, 'tcx> {
    fn new(
        module: &'ll ll::Module<'ll>,
        function: ll::FunctionValue<'ll>,
        cctxt: &'a mut CodegenCtxt<'ll, 'tcx>
    ) -> Self {
        let builder = module.get_context().create_builder();
        Self {
            tcx: cctxt.tcx,
            module,
            builder,
            function,
            cctxt,
            reg_translations: IndexVec::new(),
            block_translations: IndexVec::new()
        }
    }

    fn load_value(&mut self, place: Place<'ll>, layout: TyLayoutTuple<'tcx>) -> Value<'ll, 'tcx> {
        match layout.repr {
            layout::BackendRepr::Scalar(_) => {
                let llvm_ty: ll::BasicTypeEnum<'ll> = layout.llvm_type(self.cctxt).force_into();
                let value = ensure!(self.builder.build_load(llvm_ty, place.value, ""));
                value.as_instruction_value()
                    .unwrap()
                    .set_alignment(place.align.in_bytes() as u32)
                    .unwrap();
                Value {
                    kind: ValueKind::Immediate(value.as_basic_value_enum()),
                    layout
                }
            }
            layout::BackendRepr::ScalarPair(scalar1, scalar2) => {
                let llvm_ty: ll::BasicTypeEnum<'ll> = scalar1.llvm_type(self.cctxt).force_into();

                let mut ptr = place.value;

                let value1 = ensure!(self.builder.build_load(llvm_ty, ptr, ""));
                value1.as_instruction_value()
                    .unwrap()
                    .set_alignment(place.align.in_bytes() as u32)
                    .unwrap();

                let align = scalar2.align(self.cctxt);
                let offset = scalar1.size(self.cctxt).align_up(align);
                let offset = self.cctxt.context.i32_type().const_int(offset, false);

                ptr = unsafe {
                    ensure!(self.builder.build_in_bounds_gep(
                        self.cctxt.context.i8_type(),
                        ptr,
                        &[offset],
                        ""
                    ))
                };

                let llvm_ty: ll::BasicTypeEnum<'ll> = scalar2.llvm_type(self.cctxt).force_into();

                let value2 = ensure!(self.builder.build_load(llvm_ty, ptr, ""));
                value2.as_instruction_value()
                    .unwrap()
                    .set_alignment(place.align.in_bytes() as u32)
                    .unwrap();

                Value {
                    kind: ValueKind::Pair(value1.as_basic_value_enum(), value2.as_basic_value_enum()),
                    layout
                }
            }
            layout::BackendRepr::Memory => {
                Value {
                    kind: ValueKind::Ref(place),
                    layout
                }
            }
        }
    }

    fn alloca_place(&mut self, layout: TyLayoutTuple<'tcx>) -> Place<'ll> {
        let align = layout.align;
        let ty: ll::BasicTypeEnum<'ll> = layout.llvm_type(self.cctxt).force_into();
        let pointer = ensure!(self.builder.build_alloca(ty, ""));
        pointer
            .as_instruction()
            .unwrap()
            .set_alignment(align.in_bytes() as u32)
            .unwrap();
        
        Place { value: pointer, align }
    }

    fn lower_place(&mut self, ir_place: intermediate::Place<'tcx>) -> (Place<'ll>, TyLayoutTuple<'tcx>) {
        use intermediate::PtrTranslation::*;
        let target = ir_place.origin;
        let mut translation_chain = ir_place.translation_chain;
        let (mut cg_place, mut ty) = match self.reg_translations[target] {
            LocalKind::Place { place, layout: ty } => (place, ty),
            LocalKind::Value(value) => {
                let Some(Deref) = ir_place.translation_chain.first() else {
                    panic!("only Place::Deref makes a LocalKind::Value here");
                };
                translation_chain = &ir_place.translation_chain[1..];
                value.deref(self)
            }
            LocalKind::Dangling => panic!("tried to resolve a LocalKind::Dangling")
        };
        for translation in translation_chain {
            (cg_place, ty) = match translation {
                Deref => {
                    let value = self.load_value(cg_place, ty);
                    value.deref(self)
                },
                Field { field, ty: res_ty } => {
                    let llvm_ty: ll::BasicTypeEnum<'ll> = ty.llvm_type(self.cctxt)
                        .force_into();

                    let value = ensure!(self.builder.build_struct_gep(llvm_ty, cg_place.value, field.raw(), ""));
                    let res_layout = self.tcx.layout_of(*res_ty).unwrap();
                    (Place { value, align: res_layout.align }, res_layout)
                }
                Index { idx } => {
                    let element = match ty.ty {
                        Ty(TyKind::Array(element, ..)) => *element,
                        element => element,
                    };
                    let element = self.tcx.layout_of(element).unwrap();
                    let ptr = cg_place.value;
                    let llvm_element: ll::BasicTypeEnum<'ll> = element.llvm_type(self.cctxt).force_into();
                    let Value { kind: ValueKind::Immediate(idx), .. } = self.lower_operand(*idx) else {
                        panic!("ValueKinds other than ValueKind::Immediate is not valid on Place::Index");
                    };
                    let idx: ll::IntValue<'ll> = idx.force_into();

                    let value = ensure!(unsafe { self.builder.build_in_bounds_gep(llvm_element, ptr, &[idx], "") });
                    (Place {
                        value,
                        align: element.align
                    }, element)
                }
            };
        }
        (cg_place, ty)
    }

    fn lower_const_value(&mut self, cnst: layout::Const<'tcx>) -> Value<'ll, 'tcx> {
        let layout::Const::Value { value, ty } = cnst else {
            unreachable!("unevaluated Const's should not be appearning during code gen")
        };
        match value {
            layout::ConstValue::Scalar(value) => {
                let layout = self.tcx.layout_of(ty).unwrap();
                let ll_ty = layout.llvm_type(self.cctxt);
                match ll_ty {
                    ll::AnyTypeEnum::IntType(int_ty) => {
                        // should take care of Bool, Char and any Integer
                        let sign_extend = if let Ty(TyKind::Int(_integer, signed)) = layout.ty {
                            *signed
                        } else {
                            false
                        };

                        let value = int_ty.const_int(value.data, sign_extend).as_basic_value_enum();
                        return Value {
                            kind: ValueKind::Immediate(value),
                            layout
                        };
                    }
                    ll::AnyTypeEnum::FloatType(float_ty) => {
                        let value: f64 = unsafe { std::mem::transmute(value.data) };
                        let value = float_ty.const_float(value).as_basic_value_enum();
                        return Value {
                            kind: ValueKind::Immediate(value),
                            layout
                        };
                    }
                    _ => panic!("these types are more like aggregates and should be handled via global_alloc"),
                }
            }
            layout::ConstValue::Memory { data, align } => {
                todo!("handle global data: maybe there should be some simple way to ensure its unique")
            }
            layout::ConstValue::ZeroSized => unreachable!("ZeroSized values aren't real values")
        }
    }

    // fn handle_dependency(&mut self, global: type_ir::Global<'tcx>) -> DependencyKind<'ll> {
    //     let name = global.get_name(self.tcx);
    //     let global_value = if global.is_function() {
    //         self.module.get_function(name.get()).map(DependencyKind::Function)
    //     } else {
    //         self.module.get_global(name.get()).map(DependencyKind::Global)
    //     };

    //     if let Some(global_value) = global_value {
    //         return global_value;
    //     }

    //     if let Some(def) = global.definition() {
    //         return self.cctxt.push_dependency(def, global.initializer(), Some(self.module));
    //     }

    //     match global {
    //         type_ir::Global(type_ir::GlobalKind::Indirect { allocation, align, .. }) => {
    //             let llvm_ty = self.cctxt.context.i8_type().array_type(allocation.len() as u32);

    //             let global = self.module.add_global(llvm_ty, None, name.get());
    //             global.set_initializer(&self.cctxt.create_array_value(&allocation));
    //             global.set_alignment(align.in_bytes() as u32);
    //             global.set_linkage(ll::Linkage::Private);
    //             DependencyKind::Global(global)
    //         }
    //         type_ir::Global(type_ir::GlobalKind::EnumVariant { def }) => {
    //             let (ty, variant) = self.tcx.enum_variant(*def);
    //             let layout = self.tcx.layout_of(ty).unwrap();
    //             let llvm_ty = layout.llvm_type(self.cctxt).into_int_type();

    //             let discriminant = variant.discriminant();
    //             let type_ir::BackendRepr::Scalar(Scalar::Int(_, signed)) = layout.repr else { unreachable!() };
    //             let llvm_discriminant = llvm_ty.const_int(discriminant as u64, signed);

    //             DependencyKind::Const(llvm_discriminant.as_basic_value_enum())
    //         }
    //         _ => unreachable!()
    //     }
    // }

    // /// Loads any global except for functions
    // fn lower_global(&mut self, global: type_ir::Global<'tcx>) -> Value<'ll, 'tcx> { 
    //     let value = match self.handle_dependency(global) {
    //         DependencyKind::Global(value) => value,
    //         DependencyKind::Const(value) => {
    //             let ty = global.ty(self.tcx);
    //             let layout = self.tcx.layout_of(ty).unwrap();
    //             return Value {
    //                 kind: ValueKind::Immediate(value),
    //                 layout
    //             };
    //         }
    //         DependencyKind::Function(..) => panic!("lower_global won't lower functions")
    //     };
    //     let ty = global.ty(self.tcx);
    //     let value = value.as_pointer_value();

    //     match ty {
    //         Ty(TyKind::String) => {
    //             let layout = self.tcx.layout_of(ty).unwrap();
    //             let type_ir::Global(type_ir::GlobalKind::Indirect { allocation, ..}) = global else {
    //                 unreachable!()
    //             };
    //             let nuint_layout = self.tcx.layout_of(self.tcx.basic_types.nuint).unwrap();
    //             let nuint_type = nuint_layout.llvm_type(self.cctxt).into_int_type();

    //             let size = nuint_type.const_int(allocation.len() as u64, false);

    //             let value = Value {
    //                 kind: ValueKind::Pair(value.as_basic_value_enum(), size.as_basic_value_enum()),
    //                 layout,
    //             };
    //             value
    //         }
    //         _ => {
    //             let layout = self.tcx.layout_of(Ty::new_refrence(self.tcx, ty)).unwrap();
    //             let value = Value {
    //                 kind: ValueKind::Immediate(value.as_basic_value_enum()),
    //                 layout,
    //             };
    //             value
    //         }
    //     }
    // }

    fn get_function(&mut self, _instance: type_ir::Instance<'tcx>) -> (ll::FunctionValue<'ll>, TyLayoutTuple<'tcx>) {
        todo!("get function from instance")
        // let DependencyKind::Function(function) = self.handle_dependency(global) else {
        //     panic!("get_function won't lower non-functions");
        // };
        // let ty = ;
        // let layout = self.tcx.layout_of(ty).unwrap();
        // return (function, layout);
    }

    fn extract_function(&self, callee: intermediate::Operand<'tcx>) -> type_ir::Instance<'tcx> {
        let intermediate::Operand::Const(
            layout::Const::Value {
                value: layout::ConstValue::ZeroSized,
                ty: Ty(type_ir::TyKind::Function(def, args))
            }
        ) = callee else {
            unreachable!("function pointers aren't supported at the moment");
        };
        type_ir::Instance { def: *def, args: *args }
    }

    fn lower_operand(&mut self, operand: intermediate::Operand<'tcx>) -> Value<'ll, 'tcx> {
        match operand {
            intermediate::Operand::Copy(ir_place) => {
                let (cg_place, ty) = self.lower_place(ir_place);
                self.load_value(cg_place, ty)
            },
            intermediate::Operand::Const(cnst) => self.lower_const_value(cnst),
        }
    }

    fn visit_statement(&mut self, statement: &'tcx intermediate::Statement<'tcx>) {
        let deferred = match statement.place {
            Some(place) if let LocalKind::Dangling = self.reg_translations[place.origin] && place.translation_chain.is_empty() =>
                DeferredStorage::Initialize(place.origin),
            Some(place) => {
                let (cg_place, ty) = self.lower_place(place);
                DeferredStorage::Place { place: cg_place, layout: ty }
            }
            None => DeferredStorage::None,
        };

        match statement.rhs {
            intermediate::RValue::Ref(ir_place) => {
                let (cg_place, mut layout) = self.lower_place(ir_place);
                layout = self.tcx.layout_of(Ty::new_refrence(self.tcx, layout.ty)).unwrap();
                let value = Value {
                    kind: ValueKind::Immediate(cg_place.value.as_basic_value_enum()),
                    layout,
                };
                deferred.store_or_init(value, self);
            }
            intermediate::RValue::Use(operand) => {
                let value = self.lower_operand(operand);
                deferred.store_or_init(value, self);
            }
            intermediate::RValue::Call { callee, ref args } => {
                // FIXME: accept that this is optional and handle cases like fnptrs and intrinsic
                // calls

                let instance = self.extract_function(callee);
                let sig = self.tcx.fn_sig(instance.def).instantiate(instance.args, self.tcx);

                if sig.intrinsic {
                    let value = self.build_intrinsic_call(sig.name, args); 
                    deferred.store_or_init(
                        value,
                        self
                    );
                    return;
                }

                let (llfunc, _layout) = self.get_function(instance);

                let mut arguments = vec![];
                for (idx, param) in sig.params.iter().enumerate() {
                    let value = args[idx];
                    let value = self.lower_operand(value.operand);

                    let layout = self.tcx.layout_of(param.ty).unwrap();
                    match (value.kind, layout.repr) {
                        (ValueKind::Immediate(value), layout::BackendRepr::Scalar(..)) =>
                            arguments.push(value.force_into()),
                        (ValueKind::Pair(value1, value2), layout::BackendRepr::ScalarPair(..)) => {    
                            arguments.push(value1.force_into());
                            arguments.push(value2.force_into());
                        }
                        (ValueKind::Ref(place), layout::BackendRepr::Memory) => {
                            // copy the place to a temporary location, so that mutations done in
                            // to it in the callee don't affect us, the caller
                            
                            let tmp = self.alloca_place(value.layout);
                            let place_value = self.load_value(place, value.layout);
                            place_value.store(tmp, value.layout, self);

                            arguments.push(tmp.value.into());
                        }
                        (kind, repr) => panic!("Value representaion should correspond to Layout represenation {kind:?}, {repr:?}"),
                    }
                }

                let result_ty = sig.returns;
                let result_layout = self.tcx.layout_of(result_ty).unwrap();

                let mut ll_result = None;
                let mut mem_argload = None;
                match result_layout.repr {
                    layout::BackendRepr::Scalar(..) =>
                        ll_result = Some(()),
                    layout::BackendRepr::ScalarPair(_, scalar2) => {
                        ll_result = Some(());

                        let arg_layout = self.tcx.layout_of(scalar2.get_type(self.tcx)).unwrap();
                        let tmp = self.alloca_place(arg_layout);
                        arguments.push(tmp.value.into());

                        mem_argload = Some((tmp, arg_layout));
                    }
                    layout::BackendRepr::Memory => {
                        // FIXME: For now this is fine, but since we might store into a place at
                        // the end anyway, there are cases where we could skip allocating the
                        // temporary and go straight to the provided place
                        // NOTE: this won't work for ScalarPairs as thier types won't match
                        if result_layout.size.in_bytes > 0 {
                            let tmp = self.alloca_place(result_layout);
                            arguments.push(tmp.value.into());

                            mem_argload = Some((tmp, result_layout));
                        }
                    }
                }

                let result = ensure!(self.builder.build_call(llfunc, &arguments, ""));
                let result = ll_result.map(|()| result);

                let value = match (result, mem_argload) {
                    (Some(result), None) => { // scalar return
                        Value {
                            kind: ValueKind::Immediate(result.try_as_basic_value().unwrap_left()),
                            layout: result_layout
                        }
                    }
                    (Some(result), Some((sideload, layout))) => { // scalar pair return
                        let Value { kind: ValueKind::Immediate(llval), .. } = self.load_value(sideload, layout) else {
                            unreachable!()
                        };
                        Value {
                            kind: ValueKind::Pair(result.try_as_basic_value().unwrap_left(), llval),
                            layout: result_layout
                        }
                    }
                    (None, Some((memload, layout))) => { // memory return
                        Value {
                            kind: ValueKind::Ref(memload),
                            layout
                        }
                    }
                    (None, None) => return
                };

                deferred.store_or_init(
                    value,
                    self
                );
            }
            intermediate::RValue::BinaryOp { lhs, rhs, op } => {
                use intermediate::BinaryOp;

                let Value { kind: ValueKind::Immediate(lhs), layout: lhs_layout } = self.lower_operand(lhs) else {
                    panic!("RValue::BinaryOp is only valid for ValueKind::Immediate");
                };
                let Value { kind: ValueKind::Immediate(rhs), layout: rhs_layout } = self.lower_operand(rhs) else {
                    panic!("RValue::BinaryOp is only valid for ValueKind::Immediate");
                };
                match (lhs_layout.ty, rhs_layout.ty, op) {
                    (lhs_ty, rhs_ty, BinaryOp::Mul | BinaryOp::Add | BinaryOp::Sub) 
                        if let Ty(TyKind::Int(_, signed)) = lhs_ty && lhs_ty == rhs_ty => {
                        // this is a normal integer addition, mutliplication or subtraction
                        let lhs: ll::IntValue<'ll> = lhs.force_into();
                        let rhs: ll::IntValue<'ll> = rhs.force_into();

                        let res = base_case_handler! {
                            "build_int_"
                            >> match signed {
                                true => "nsw_",
                                false => ""
                            }
                            >> match op {
                                BinaryOp::Mul => "mul",
                                BinaryOp::Add => "add",
                                BinaryOp::Sub => "sub",
                                _ => unreachable!()
                            }
                            => {
                                ensure!(self.builder.$token(lhs, rhs, ""))
                            }
                        };
                        let res = Value {
                            kind: ValueKind::Immediate(res.into()),
                            layout: lhs_layout
                        };
                        deferred.store_or_init(res, self);
                    }
                    (lhs_ty, _rhs_ty, BinaryOp::Div | BinaryOp::Rem) 
                        if let Ty(TyKind::Int(_, signed)) = lhs_ty => {
                        // this is a normal integer division and remainder
                        let lhs: ll::IntValue<'ll> = lhs.force_into();
                        let rhs: ll::IntValue<'ll> = rhs.force_into();

                        let res = base_case_handler! {
                            "build_int_"
                            >> match signed {
                                true => "signed_",
                                false => "unsigned_"
                            }
                            >> match op {
                                BinaryOp::Div => "div",
                                BinaryOp::Rem => "rem",
                                _ => unreachable!()
                            }
                            => {
                                ensure!(self.builder.$token(lhs, rhs, ""))
                            }
                        };
                        let res = Value {
                            kind: ValueKind::Immediate(res.into()),
                            layout: lhs_layout
                        };
                        deferred.store_or_init(res, self);
                    }
                    (lhs_ty, _rhs_ty, BinaryOp::Shr) 
                        if let Ty(TyKind::Int(_, signed)) = lhs_ty => {
                        let lhs: ll::IntValue<'ll> = lhs.force_into();
                        let rhs: ll::IntValue<'ll> = rhs.force_into();

                        let res = ensure!(self.builder.build_right_shift(lhs, rhs, *signed, ""));
                        let res = Value {
                            kind: ValueKind::Immediate(res.into()),
                            layout: lhs_layout
                        };
                        deferred.store_or_init(res, self);
                    }
                    (lhs_ty, _rhs_ty, BinaryOp::Shl | BinaryOp::Xor | BinaryOp::Or | BinaryOp::And) 
                        if let Ty(TyKind::Int(..)) = lhs_ty => {
                        let lhs: ll::IntValue<'ll> = lhs.force_into();
                        let rhs: ll::IntValue<'ll> = rhs.force_into();

                        let res = base_case_handler! {
                            "build_"
                            >> match op {
                                BinaryOp::Shl => "left_shift",
                                BinaryOp::Xor => "xor",
                                BinaryOp::Or => "or",
                                BinaryOp::And => "and",
                                _ => unreachable!()
                            }
                            => {
                                ensure!(self.builder.$token(lhs, rhs, ""))
                            }
                        };
                        let res = Value {
                            kind: ValueKind::Immediate(res.into()),
                            layout: lhs_layout
                        };
                        deferred.store_or_init(res, self);
                    }
                    (lhs_ty, _rhs_ty, BinaryOp::Eq | BinaryOp::Ne) 
                        if let Ty(TyKind::Int(..)) = lhs_ty => {
                        let lhs: ll::IntValue<'ll> = lhs.force_into();
                        let rhs: ll::IntValue<'ll> = rhs.force_into();

                        let predicate = match op {
                            BinaryOp::Eq => ll::IntPredicate::EQ,
                            BinaryOp::Ne => ll::IntPredicate::NE,
                            _ => unreachable!()
                        };

                        let res = ensure!(self.builder.build_int_compare(predicate, lhs, rhs, ""));
                        let res = Value {
                            kind: ValueKind::Immediate(res.into()),
                            layout: self.tcx.layout_of(self.tcx.basic_types.bool).unwrap()
                        };
                        deferred.store_or_init(res, self);
                    }
                    (lhs_ty, _rhs_ty, BinaryOp::Gt | BinaryOp::Ge | BinaryOp::Lt | BinaryOp::Le) 
                        if let Ty(TyKind::Int(.., signed)) = lhs_ty => {
                        let lhs: ll::IntValue<'ll> = lhs.force_into();
                        let rhs: ll::IntValue<'ll> = rhs.force_into();

                        let predicate = base_case_handler! {
                            ""
                            >> match signed {
                                true => "S",
                                false => "U"
                            }
                            >> match op {
                                BinaryOp::Gt => "GT",
                                BinaryOp::Ge => "GE",
                                BinaryOp::Lt => "LT",
                                BinaryOp::Le => "LE",
                                _ => unreachable!()
                            }
                            => {
                                ll::IntPredicate::$token
                            }
                        };
                        let res = ensure!(self.builder.build_int_compare(predicate, lhs, rhs, ""));
                        let res = Value {
                            kind: ValueKind::Immediate(res.into()),
                            layout: self.tcx.layout_of(self.tcx.basic_types.bool).unwrap()
                        };
                        deferred.store_or_init(res, self);
                    }
                    (lhs_ty, _rhs_ty, BinaryOp::Mul | BinaryOp::Div | BinaryOp::Rem | BinaryOp::Add | BinaryOp::Sub) 
                        if let Ty(TyKind::Float(_)) = lhs_ty => {
                        let lhs: ll::FloatValue<'ll> = lhs.force_into();
                        let rhs: ll::FloatValue<'ll> = rhs.force_into();

                        let res = base_case_handler! {
                            "build_float_"
                            >> match op {
                                BinaryOp::Mul => "mul",
                                BinaryOp::Div => "div",
                                BinaryOp::Rem => "rem",
                                BinaryOp::Add => "add",
                                BinaryOp::Sub => "sub",
                                _ => unreachable!()
                            }
                            => {
                                ensure!(self.builder.$token(lhs, rhs, ""))
                            }
                        };
                        let res = Value {
                            kind: ValueKind::Immediate(res.into()),
                            layout: lhs_layout
                        };
                        deferred.store_or_init(res, self);
                    }
                    (lhs_ty, _rhs_ty, BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Gt | BinaryOp::Ge | BinaryOp::Lt | BinaryOp::Le) 
                        if let Ty(TyKind::Float(_)) = lhs_ty => {
                        let lhs: ll::FloatValue<'ll> = lhs.force_into();
                        let rhs: ll::FloatValue<'ll> = rhs.force_into();

                        let predicate = match op {
                            BinaryOp::Eq => ll::FloatPredicate::OEQ,
                            BinaryOp::Ne => ll::FloatPredicate::ONE,
                            BinaryOp::Gt => ll::FloatPredicate::OGT,
                            BinaryOp::Ge => ll::FloatPredicate::OGE,
                            BinaryOp::Lt => ll::FloatPredicate::OLT,
                            BinaryOp::Le => ll::FloatPredicate::OLE,
                            _ => unreachable!()
                        };
                        let res = ensure!(self.builder.build_float_compare(predicate, lhs, rhs, ""));
                        let res = Value {
                            kind: ValueKind::Immediate(res.into()),
                            layout: self.tcx.layout_of(self.tcx.basic_types.bool).unwrap()
                        };
                        deferred.store_or_init(res, self);
                    }
                    (lhs_ty, rhs_ty, BinaryOp::Add | BinaryOp::Sub) 
                        if let Ty(TyKind::Refrence(ref_ty)) = lhs_ty && let Ty(TyKind::Int(..)) = rhs_ty => {
                        let lhs: ll::PointerValue<'ll> = lhs.force_into();
                        let mut rhs: ll::IntValue<'ll> = rhs.force_into();

                        if op == BinaryOp::Sub {
                            rhs = ensure!(self.builder.build_int_nsw_sub(rhs.get_type().const_int(0, false), rhs, ""));
                        }

                        let llvm_ty = match ref_ty {
                            Ty(TyKind::Void) => self.cctxt.context.i8_type().as_basic_type_enum(),
                            _ => self.tcx.layout_of(*ref_ty).unwrap().llvm_type(self.cctxt).force_into()
                        };

                        let res = ensure!(unsafe { self.builder.build_in_bounds_gep(llvm_ty, lhs, &[rhs], "") });
                        let res = Value {
                            kind: ValueKind::Immediate(res.into()),
                            layout: lhs_layout
                        };
                        deferred.store_or_init(res, self);
                    }
                    (lhs_ty, rhs_ty, BinaryOp::Sub) 
                        if let Ty(TyKind::Refrence(_)) = lhs_ty && lhs_ty == rhs_ty => {
                        let lhs: ll::PointerValue<'ll> = lhs.force_into();
                        let rhs: ll::PointerValue<'ll> = rhs.force_into();

                        let res = ensure!(self.builder.build_int_sub(lhs, rhs, ""));
                        let res = Value {
                            kind: ValueKind::Immediate(res.into()),
                            layout: self.tcx.layout_of(self.tcx.basic_types.nuint).unwrap()
                        };
                        deferred.store_or_init(res, self);
                    }
                    (lhs_ty, _rhs_ty, BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Gt | BinaryOp::Ge | BinaryOp::Lt | BinaryOp::Le) 
                        if let Ty(TyKind::Refrence(_)) = lhs_ty => {
                        let lhs: ll::PointerValue<'ll> = lhs.force_into();
                        let rhs: ll::PointerValue<'ll> = rhs.force_into();

                        let predicate = match op {
                            BinaryOp::Eq => ll::IntPredicate::EQ,
                            BinaryOp::Ne => ll::IntPredicate::NE,
                            BinaryOp::Gt => ll::IntPredicate::UGT,
                            BinaryOp::Ge => ll::IntPredicate::UGE,
                            BinaryOp::Lt => ll::IntPredicate::ULT,
                            BinaryOp::Le => ll::IntPredicate::ULE,
                            _ => unreachable!()
                        };
                        let res = ensure!(self.builder.build_int_compare(predicate, lhs, rhs, ""));
                        let res = Value {
                            kind: ValueKind::Immediate(res.into()),
                            layout: self.tcx.layout_of(self.tcx.basic_types.bool).unwrap()
                        };
                        deferred.store_or_init(res, self);
                    }
                    (lhs_ty, rhs_ty, op) =>
                        panic!("{op:?} is not defined between {lhs_ty:?} and {rhs_ty:?} and should not be caught here"),
                }

            }
            intermediate::RValue::Cast { value, ty: res_ty } => {
                let result_layout = self.tcx.layout_of(res_ty).unwrap(); 
                let Value { kind: value_kind, layout: val_layout } = self.lower_operand(value); 
                let llvm_value = match value_kind {
                    ValueKind::Immediate(llvm_value) => llvm_value,
                    ValueKind::Ref(place) if let Ty(TyKind::Array(..)) = val_layout.ty && let Ty(TyKind::Refrence(..)) = res_ty => {
                        let res = Value {
                            kind: ValueKind::Immediate(place.value.as_basic_value_enum()),
                            layout: result_layout
                        };
                        deferred.store_or_init(res, self);
                        return;
                    }
                    kind => panic!("RValue::Cast is not defined for {kind:?}"),
                };
                let res = match (val_layout.ty, res_ty) {
                    (Ty(TyKind::Int(..)), Ty(TyKind::Int(_, signed))) => {
                        let int_value: ll::IntValue<'ll> = llvm_value.force_into();
                        let int_type: ll::IntType<'ll> = result_layout.llvm_type(self.cctxt)
                            .force_into();
                        ensure!(self.builder.build_int_cast_sign_flag(int_value, int_type, *signed, ""))
                            .as_basic_value_enum()
                    }
                    (Ty(TyKind::Float(..)), Ty(TyKind::Float(..))) => {
                        let float_value: ll::FloatValue<'ll> = llvm_value.force_into();
                        let float_type: ll::FloatType<'ll> = result_layout.llvm_type(self.cctxt)
                            .force_into();
                        ensure!(self.builder.build_float_cast(float_value, float_type, ""))
                            .as_basic_value_enum()
                    }
                    (Ty(TyKind::Int(_, signed)), Ty(TyKind::Float(..))) => {
                        let int_value: ll::IntValue<'ll> = llvm_value.force_into();
                        let float_type: ll::FloatType<'ll> = result_layout.llvm_type(self.cctxt)
                            .force_into();

                        let res = base_case_handler! {
                            "build_"
                            >> match signed {
                                true => "signed_int_to_float",
                                false => "unsigned_int_to_float"
                            }
                            => {
                                ensure!(self.builder.$token(int_value, float_type, ""))
                            }
                        };
                        res.as_basic_value_enum()
                    }
                    (Ty(TyKind::Int(type_ir::Integer::I8, false)), Ty(TyKind::Bool)) => llvm_value,
                    (Ty(TyKind::Int(type_ir::Integer::I32, false)), Ty(TyKind::Char)) => llvm_value,
                    (Ty(TyKind::Refrence(_)), Ty(TyKind::Int(..))) => {
                        let pointer_value: ll::PointerValue<'ll> = llvm_value.force_into();
                        let int_type: ll::IntType<'ll> = result_layout.llvm_type(self.cctxt)
                            .force_into();

                        ensure!(self.builder.build_ptr_to_int(pointer_value, int_type, "")).as_basic_value_enum()
                    },
                    (val_ty, res_ty) =>
                        panic!("casting is not defined from {val_ty:?} to {res_ty:?} and should not be caught here"),
                };
                let res = Value {
                    kind: ValueKind::Immediate(res),
                    layout: result_layout
                };
                deferred.store_or_init(res, self);
            }
            intermediate::RValue::Invert(value) => {
                let Value { kind: ValueKind::Immediate(value), layout } = self.lower_operand(value) else {
                    panic!("RValue::Invert is only valid for ValueKind::Immediate");
                };
                let value: ll::IntValue<'ll> = value.force_into();
                let res = ensure!(self.builder.build_not(value, ""));
                let res = Value {
                    kind: ValueKind::Immediate(res.as_basic_value_enum()),
                    layout
                };
                deferred.store_or_init(res, self);
            }
            intermediate::RValue::Negate(value) => {
                let Value { kind: ValueKind::Immediate(value), layout } = self.lower_operand(value) else {
                    panic!("RValue::Negate is only valid for ValueKind::Immediate");
                };
                let res = match layout.ty {
                    Ty(TyKind::Int(..)) => {
                        let value: ll::IntValue<'ll> = value.force_into();
                        let res = ensure!(self.builder.build_int_nsw_sub(value.get_type().const_int(0, false), value, ""));
                        res.as_basic_value_enum()
                    }
                    Ty(TyKind::Float(_)) => {
                        let value: ll::FloatValue<'ll> = value.force_into();
                        let res = ensure!(self.builder.build_float_neg(value, ""));
                        res.as_basic_value_enum()
                    }
                    ty => panic!("Cannot negate {ty:?}"),
                };
                let res = Value {
                    kind: ValueKind::Immediate(res),
                    layout
                };
                deferred.store_or_init(res, self);
            }
            intermediate::RValue::ExplicitInit { ty, ref initializers } => {
                let layout = self.tcx.layout_of(ty).unwrap();
                let (dest, deferred) = deferred.dissolve();
                let dest = dest.map_or_else(|| self.alloca_place(layout), |(place, _)| place);
                match ty {
                    Ty(TyKind::Array(element, _count)) => {
                        let element_layout = self.tcx.layout_of(*element).unwrap();
                        let layout::Fields::Array { count, .. } = element_layout.layout.fields else {
                            unreachable!()
                        };
                        if initializers.len() == 1 {
                            let default = self.lower_operand(initializers[0].1.operand);
                            let id = (statement as *const intermediate::Statement<'tcx>).addr() as u16;
                            self.default_initialize_array(dest, element_layout, default, count, id);
                        } else {
                            debug_assert!(initializers.len() as u64 == count);
                            self.initialize_with_initializers(dest, element_layout, initializers, false);
                        }
                    }
                    Ty(TyKind::Adt(AdtDef(AdtKind::Struct(..)), _)) => {
                        self.initialize_with_initializers(dest, layout, initializers, true);
                    }
                    _ => panic!("can't explicit init {ty:?}"),
                }
                if let Some(deferred) = deferred {
                    let value = self.load_value(dest, layout);
                    deferred.store_or_init(value, self);
                }
            }
        }
    }

    fn build_intrinsic_call(&mut self, name: symbol::Symbol, args: &[intermediate::SpanOperand<'tcx>]) -> Value<'ll, 'tcx> {
        match name {
            sym::main => todo!("fetch defined entrypoint and build stub in cases of non-signature match"),
            sym::stringlen => {
                let mut args = args.iter();
                let Some(string) = args.next() else { unreachable!() };
                let Value { kind: ValueKind::Pair(_data, len), layout } = self.lower_operand(string.operand) else {
                    unreachable!();
                };
                debug_assert!(layout.ty == self.tcx.basic_types.string);
                debug_assert!(len.is_int_value());

                Value {
                    kind: ValueKind::Immediate(len),
                    layout: self.tcx.layout_of(self.tcx.basic_types.nuint).unwrap()
                }
            }
            sym::stringdata => {
                let mut args = args.iter();
                let Some(string) = args.next() else { unreachable!() };
                let Value { kind: ValueKind::Pair(data, _len), layout } = self.lower_operand(string.operand) else {
                    unreachable!();
                };
                debug_assert!(layout.ty == self.tcx.basic_types.string);
                debug_assert!(data.is_pointer_value());

                Value {
                    kind: ValueKind::Immediate(data),
                    layout: self.tcx.layout_of(Ty::new_refrence(self.tcx, self.tcx.basic_types.byte)).unwrap()
                }
            }
            sym::string_from_raw_parts => {
                let mut args = args.iter();
                let Some(data) = args.next() else { unreachable!() };
                let Some(len) = args.next() else { unreachable!() };

                let Value { kind: ValueKind::Immediate(data), .. } = self.lower_operand(data.operand) else {
                    unreachable!();
                };
                let Value { kind: ValueKind::Immediate(len), .. } = self.lower_operand(len.operand) else {
                    unreachable!();
                };
                debug_assert!(data.is_pointer_value());
                debug_assert!(len.is_int_value());

                Value {
                    kind: ValueKind::Pair(data, len),
                    layout: self.tcx.layout_of(self.tcx.basic_types.string).unwrap()
                }
            }
            _ => panic!("{name} is not a known intrinsic"),
        }
    }

    fn initialize_with_initializers(
        &mut self,
        dest: Place<'ll>,
        layout: TyLayoutTuple<'tcx>,
        initializers: &[(type_ir::FieldIdx, intermediate::SpanOperand<'tcx>)],
        is_struct: bool
    ) {
        let llvm_ty: ll::BasicTypeEnum<'ll> = layout.llvm_type(self.cctxt).force_into();
        for init in initializers {
            let value = self.lower_operand(init.1.operand);
            let (element_pointer, element_layout) = if is_struct {
                let ptr = ensure!(self.builder.build_struct_gep(llvm_ty, dest.value, init.0.raw(), ""));
                let Ty(TyKind::Adt(AdtDef(AdtKind::Struct(strct)), _)) = layout.ty else {
                    unreachable!("ty is not struct")
                };
                let field = strct.get_field(init.0);
                let field_ty = self.tcx.type_of(field.def);
                let field_layout = self.tcx.layout_of(field_ty).unwrap();

                (ptr, field_layout)
            } else {
                let idx = self.cctxt.context.i32_type().const_int(init.0.raw() as u64, false);
                let ptr = ensure!(unsafe { self.builder.build_in_bounds_gep(llvm_ty, dest.value, &[idx], "") });

                (ptr, layout)
            };
            let place = Place {
                value: element_pointer,
                align: element_layout.align
            };
            value.store(place, element_layout, self);
        }
    }

    fn default_initialize_array(&mut self, dest: Place<'ll>, layout: TyLayoutTuple<'tcx>, default: Value<'ll, 'tcx>, count: u64, id: u16) {
        if count == 0 {
            return;
        }
        if count == 1 {
            default.store(dest, layout, self);
            return;
        }

        let llvm_element: ll::BasicTypeEnum<'ll> = layout.llvm_type(self.cctxt).force_into();
        let llvm_index: ll::IntType<'ll> = self.tcx.layout_of(self.tcx.basic_types.nuint)
            .unwrap()
            .llvm_type(self.cctxt).force_into();

        let begin = self.builder.get_insert_block().unwrap();

        let context = self.module.get_context();
        let loop_body = context.append_basic_block(self.function, &format!("init_array_loop_body_{id:x}"));
        let loop_end = context.append_basic_block(self.function, &format!("init_array_loop_done_{id:x}"));

        ensure!(self.builder.build_unconditional_branch(loop_body));
        self.builder.position_at_end(loop_body);

        let phi_idx = ensure!(self.builder.build_phi(llvm_index, &format!("idx_{id:x}")));

        let idx = phi_idx.as_basic_value().force_into();
        let idx_pointer = ensure!(unsafe { self.builder.build_in_bounds_gep(llvm_element, dest.value, &[idx], "") });
        let idx_place = Place {
            value: idx_pointer,
            align: layout.align
        };
        default.store(idx_place, layout, self);

        let next_idx = ensure!(self.builder.build_int_add(idx, llvm_index.const_int(1, false), &format!("next_idx_{id:x}")));
        phi_idx.add_incoming(&[
            (&llvm_index.const_zero(), begin),
            (&next_idx, loop_body)
        ]);
        let cmp = ensure!(self.builder.build_int_compare(
            ll::IntPredicate::UGE,
            next_idx, llvm_index.const_int(count, false),
            ""
        ));
        ensure!(self.builder.build_conditional_branch(cmp, loop_end, loop_body));
        self.builder.position_at_end(loop_end);
    }

    fn visit_terminator(&mut self, terminator: &'tcx intermediate::Terminator<'tcx>, signature: type_ir::Signature<'tcx>) {
        match terminator.kind {
            intermediate::TerminatorKind::Goto(block_id) => {
                let basic_block = self.resolve_block(block_id);
                ensure!(self.builder.build_unconditional_branch(basic_block));
            }
            intermediate::TerminatorKind::Diverge { condition, true_target, false_target } => {
                let then_block = self.resolve_block(true_target);
                let else_block = self.resolve_block(false_target);
                let Value { kind: ValueKind::Immediate(comparison), .. } = self.lower_operand(condition) else {
                    panic!("cannto compare against other than ValueKind::Immediate");
                };
                ensure!(self.builder.build_conditional_branch(comparison.into_int_value(), then_block, else_block));

            }
            intermediate::TerminatorKind::Return { value } => {
                let layout = self.tcx.layout_of(signature.returns).unwrap();
                match layout.repr {
                    layout::BackendRepr::Scalar(_) => {
                        let value = self.lower_operand(value.unwrap());
                        let Value { kind: ValueKind::Immediate(value), .. } = value else {
                            panic!("ValueKind should match BackendRepr");
                        };
                        let value: ll::BasicValueEnum<'ll> = value.force_into();
                        ensure!(self.builder.build_return(Some(&value)));
                    }
                    layout::BackendRepr::ScalarPair(_scalar1, scalar2) => {

                        let value = self.lower_operand(value.unwrap());
                        let Value { kind: ValueKind::Pair(value1, value2), .. } = value else {
                            panic!("ValueKind should match BackendRepr");
                        };

                        let argument: ll::PointerValue<'ll> = self.function.get_last_param()
                            .unwrap()
                            .force_into();
                        let align = scalar2.align(self.cctxt);
                        let place = Place { value: argument, align };
                        let scalar2_layout = self.tcx.layout_of(scalar2.get_type(self.tcx)).unwrap();
                        let value2 = Value {
                            kind: ValueKind::Immediate(value2),
                            layout: scalar2_layout
                        };
                        value2.store(place, scalar2_layout, self);

                        let value1: ll::BasicValueEnum<'ll> = value1.force_into();
                        ensure!(self.builder.build_return(Some(&value1)));
                    }
                    layout::BackendRepr::Memory => {
                        if layout.size.in_bytes > 0 {
                            let value = self.lower_operand(value.unwrap());
                            let Value { kind: ValueKind::Ref(value), .. } = value else {
                                panic!("ValueKind should match BackendRepr");
                            };

                            let argument: ll::PointerValue<'ll> = self.function.get_last_param()
                                .unwrap()
                                .force_into();
                            let place = Place { value: argument, align: layout.align };
                            let value = Value {
                                kind: ValueKind::Ref(value),
                                layout
                            };
                            value.store(place, layout, self);
                        }
                        ensure!(self.builder.build_return(None));
                    }
                }
            }
        }
    }

    fn visit_basic_block(&mut self, block: &'tcx intermediate::BasicBlock<'tcx>, signature: type_ir::Signature<'tcx>) {
        for statement in &block.statements {
            self.visit_statement(statement);
        }
        let terminator = block.terminator
            .get()
            .expect("every IR block should be terminated");
        self.visit_terminator(terminator, signature);
    }

    fn collect_placebound_regs(body: &'tcx intermediate::Body<'tcx>) -> HashSet<intermediate::RegisterId> {
        // NOTE: (for people confused why Operand::Copy makes something placebound) LLVM cannot copy
        // values, so the only way to do it is to load and store from a Place.

        let mut placebounds = HashSet::new();
        for block in &body.basic_blocks {
            for statement in &block.statements { 
                if let intermediate::RValue::Use(intermediate::Operand::Copy(place)) | intermediate::RValue::Ref(place) = statement.rhs &&
                    let Some(reg) = get_reg(place) {
                    placebounds.insert(reg);
                }
            }
        }

        return placebounds;

        fn get_reg(place: intermediate::Place) -> Option<RegisterId> {
            use intermediate::PtrTranslation::*;
            if let Some(Deref) = place.translation_chain.first() {
                return None;
            }
            Some(place.origin)
        }
    }

    fn visit_body(&mut self, body: &'tcx intermediate::Body<'tcx>, signature: type_ir::Signature<'tcx>) {
        let placebounds = Self::collect_placebound_regs(body);

        self.reg_translations.resize_with(
            body.local_registers.len(), Default::default);

        let entry = self.resolve_block(body.entry);
        self.builder.position_at_end(entry);

        let mut arg_idx = 0;
        for (idx, param) in signature.params.iter().enumerate() {
            let idx = intermediate::RegisterId::from_usize(idx);
            let param_layout = self.tcx.layout_of(param.ty)
                .unwrap();
            let reg = &body.local_registers[idx];
            debug_assert_eq!(reg.kind, intermediate::RegKind::Param);
            match param_layout.repr {
                layout::BackendRepr::Scalar(..) => {
                    let argument = self.function.get_nth_param(arg_idx)
                        .unwrap();
                    let kind = ValueKind::Immediate(argument.into());

                    let value = Value { kind, layout: param_layout };
                    if reg.mutability == Mutability::Const && !placebounds.contains(&idx) {
                        self.reg_translations[idx] = LocalKind::Value(value);
                    } else {
                        let place = self.alloca_place(param_layout);
                        value.store(place, param_layout, self);
                        self.reg_translations[idx] = LocalKind::Place { place, layout: param_layout };
                    }
                }
                layout::BackendRepr::ScalarPair(..) => {
                    let argument1 = self.function.get_nth_param(arg_idx)
                        .unwrap();
                    let argument2 = self.function.get_nth_param(arg_idx + 1)
                        .unwrap();
                    let kind = ValueKind::Pair(argument1.into(), argument2.into());

                    let value = Value { kind, layout: param_layout };
                    if reg.mutability == Mutability::Const && !placebounds.contains(&idx) {
                        self.reg_translations[idx] = LocalKind::Value(value);
                    } else {
                        let place = self.alloca_place(param_layout);
                        value.store(place, param_layout, self);
                        self.reg_translations[idx] = LocalKind::Place { place, layout: param_layout };
                    }

                    arg_idx += 2;
                    continue;
                }
                layout::BackendRepr::Memory => {
                    let argument: ll::PointerValue<'ll> = self.function.get_nth_param(arg_idx)
                        .unwrap()
                        .force_into();
                    let align = param_layout.align;
                    let place = Place { value: argument, align };
                    self.reg_translations[idx] = LocalKind::Place { place, layout: param_layout };
                }
            }
            arg_idx += 1;
        }

        for (id, register) in body.local_registers.iter_enumerated() {
            let layout = self.tcx.layout_of(register.ty).unwrap();
            let place = self.alloca_place(layout);
            if register.kind == intermediate::RegKind::Local ||
                (register.kind == intermediate::RegKind::Temp && placebounds.contains(&id)) {
                self.reg_translations[id] = LocalKind::Place { place, layout };
            }
        }

        for (id, block) in body.basic_blocks.iter_enumerated() {
            let basic_block = self.resolve_block(id);
            self.builder.position_at_end(basic_block);
            self.visit_basic_block(block, signature);
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
        let block = context.append_basic_block(self.function, &format!("{block_id:?}"));
        self.block_translations[block_id] = Some(block);
        block
    }
}

// FIXME: the const system is yet to rigid and undynamic, needing for every trait to be explicitly
// checked in the `type_ir.rs` file. This makes it hard to add real private-trait implementations,
// as at least the trait name always has to leak outside the module.
#[allow(dead_code)]
trait LLVMConstValueConversion {
    fn convert<'ll, 'tcx>(&self, ctxt: &mut CodegenCtxt<'ll, 'tcx>) -> Value<'ll, 'tcx>;
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum DependencyState {
    Pending, Done
}

#[derive(Clone, Copy)]
struct DependencyData<'ll> {
    mangled_name: symbol::Symbol,
    module: &'ll ll::Module<'ll>,
    value: DependencyKind<'ll>,
    state: DependencyState
}

#[derive(Clone, Copy)]
enum DependencyKind<'ll> {
    Function(ll::FunctionValue<'ll>),
    Global(ll::GlobalValue<'ll>),
    Const(ll::BasicValueEnum<'ll>)
}

struct CodegenCtxt<'ll, 'tcx> {
    tcx: TyCtxt<'tcx>,
    // FIXME: this should be a TypedArena, as this way we won't leak all the `ll::Context`s and
    // thier associated modules and can properly regain ownership
    arena: &'ll bumpalo::Bump,
    context: &'ll ll::Context,
    module_map: HashMap<ast::NodeId, &'ll ll::Module<'ll>>,
    dependency_map: HashMap<ast::DefId, DependencyData<'ll>>,
    type_translation_cache: RefCell<HashMap<TyLayoutTuple<'tcx>, ll::AnyTypeEnum<'ll>>>,
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

    fn create_array_value(&mut self, data: &[u8]) -> ll::ArrayValue<'ll> {
        let byte_type = self.context.i8_type();

        let mut values = Vec::with_capacity(data.len());
        for byte in data {
            values.push(byte_type.const_int(*byte as u64, false));
        }
        let llvm_value = byte_type.const_array(&values);
        llvm_value 
    }

    fn ensure_delcartion(&mut self, value: DependencyKind<'ll>, mangled_name: symbol::Symbol, relative_module: &'ll ll::Module<'ll>) -> DependencyKind<'ll> {
        match value {
            DependencyKind::Function(func) => {
                if let Some(decl) = relative_module.get_function(mangled_name.get()) {
                    return DependencyKind::Function(decl);
                }
                let decl = relative_module.add_function(
                    mangled_name.get(),
                    func.get_type(),
                    Some(ll::Linkage::External)
                );
                DependencyKind::Function(decl)
            }
            DependencyKind::Global(global) => {
                if let Some(decl) = relative_module.get_global(mangled_name.get()) {
                    return DependencyKind::Global(decl);
                }
                let llvm_type: ll::BasicTypeEnum<'ll> = global.get_value_type().force_into();
                let decl = relative_module.add_global(
                    llvm_type,
                    None,
                    mangled_name.get(),
                );
                decl.set_externally_initialized(true);
                decl.set_linkage(ll::Linkage::External);
                decl.set_alignment(global.get_alignment());
                DependencyKind::Global(decl)
            }
            cnst @ DependencyKind::Const(_) => cnst
        }
    }

    fn push_dependency(&mut self, def: ast::DefId, init: Option<layout::Const<'tcx>>, relative_module: Option<&'ll ll::Module<'ll>>) -> DependencyKind<'ll> {
        if let Some(DependencyData { value, module, mangled_name, .. }) = self.dependency_map.get(&def) {
            if let Some(relative_module) = relative_module && relative_module != *module {
                return self.ensure_delcartion(*value, *mangled_name, relative_module);
            }
            return *value;
        }

        let node = self.tcx.node_by_def_id(def);
        let ast::Node::Item(item) = node else {
            panic!("CodegenCtxt::push_dependency is only allowed on source-bound items");
        };

        let state = if let ast::Item { kind: ast::ItemKind::Function(func), .. } = item && func.body.is_some() {
            self.depedency_queue.push_back(def);
            DependencyState::Pending
        } else {
            DependencyState::Done
        };

        let module = self.get_module_for_def(def);
        let ty = self.tcx.type_of(def);
        let layout = self.tcx.layout_of(ty).unwrap();

        let mangled_name = item.get_name(self.tcx);
        let value = match item {
            ast::Item { kind: ast::ItemKind::Function(..), .. } => {
                let function = module
                    .add_function(
                        mangled_name.get(),
                        layout.llvm_type(self).into_function_type(),
                        Some(ll::Linkage::External)
                    );
                DependencyKind::Function(function)
            }
            ast::Item { kind: ast::ItemKind::GlobalVar(..), .. } => {
                let array_ty = self.context.i8_type().array_type(layout.size.in_bytes as u32);
                let Some(layout::Const::Value { .. }) = init else {
                    unreachable!()
                };
                let global = module
                    .add_global(
                        array_ty,
                        None,
                        mangled_name.get(),
                    );
                global.set_initializer(&self.create_array_value(todo!()));
                global.set_linkage(ll::Linkage::External);
                global.set_alignment(layout.align.in_bytes() as u32);
                DependencyKind::Global(global)
            }
            ast::Item { kind, .. } => panic!("{kind:?} items are invalid in push_dependency")
        };

        let data = DependencyData {
            value, state, module, mangled_name
        };
        self.dependency_map.insert(def, data);

        if let Some(relative_module) = relative_module && relative_module != module {
            return self.ensure_delcartion(value, mangled_name, relative_module);
        }
        value
    }

    fn generate_code_bfs(&mut self) {
        while let Some(element) = self.depedency_queue.pop_front() {
            let DependencyKind::Function(value) = self.dependency_map[&element].value else {
                unreachable!("dependency queue is supposed to only contain functions");
            };
            let module = self.get_module_for_def(element);

            let body = self.tcx.build_ir(element)
                .expect("valid body should exist for codegen item");
            let sig = self.tcx.fn_sig(element);

            let mut builder = CodeBuilder::new(module, value, self);

            builder.visit_body(body, sig);

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
                let module = Self::create_module(node, self.tcx, self.context, self.arena);
                entry.insert(module)
            }
            Entry::Occupied(entry) => entry.into_mut()
        }
    }

    fn create_module(node: ast::Node<'tcx>, tcx: TyCtxt<'tcx>, context: &'ll ll::Context, arena: &'ll bumpalo::Bump) -> &'ll ll::Module<'ll> {
        let ast::Node::SourceFile(module) = node else {
            panic!("non source-level module in CodegenCtxt::create_module");
        };
        let info = tcx.module_info(module);
        Self::create_module_by_info(info, context, arena)
    }

    fn create_module_by_info(info: ModuleInfo, context: &'ll ll::Context, arena: &'ll bumpalo::Bump) -> &'ll ll::Module<'ll> {
        let module = context.create_module(info.mangled_name.get());
        module.set_source_file_name(&info.source_file_name);
        arena.alloc(module)
    }
}

trait ForceInto<R> {
    fn force_into(self) -> R;
}

impl<T: TryInto<R, Error = E>, R, E: std::fmt::Debug> ForceInto<R> for T {
    fn force_into(self) -> R {
        self.try_into().unwrap()
    }
}

impl<'ll, 'tcx> DataLayoutExt for CodegenCtxt<'ll, 'tcx> {
    fn data_layout(&self) -> &TargetDataLayout {
        &self.target_data_layout
    }
}

impl<'tcx> TyLayoutTuple<'tcx> {
    fn llvm_type<'ll>(&self, ctxt: &CodegenCtxt<'ll, 'tcx>) -> ll::AnyTypeEnum<'ll> {
        if let Some(cached) = ctxt.type_translation_cache.borrow().get(self) {
            return *cached;
        }

        let ll_type = self.lower_type_and_layout(ctxt);
        ctxt.type_translation_cache.borrow_mut().insert(*self, ll_type);

        ll_type
    }

    fn is_llvm_immediate(&self) -> bool {
        match self.repr {
            layout::BackendRepr::Scalar(..) => true,
            layout::BackendRepr::ScalarPair(..) | layout::BackendRepr::Memory => false,
        }
    }

    fn lower_type_and_layout<'ll>(&self, ctxt: &CodegenCtxt<'ll, 'tcx>) -> ll::AnyTypeEnum<'ll> {
        if let layout::BackendRepr::Scalar(scalar) = self.repr && !matches!(self.ty, Ty(TyKind::Bool)){
            return scalar.llvm_type(ctxt);
        }

        match self.ty {
            Ty(TyKind::Bool) => 
                return ll::AnyTypeEnum::IntType(ctxt.context.bool_type()),
            // TODO: is never == void ok here?
            Ty(TyKind::Void | TyKind::Never) => 
                return ll::AnyTypeEnum::VoidType(ctxt.context.void_type()),
            Ty(TyKind::Function(def, generics)) => {
                let signature = ctxt.tcx
                    .fn_sig(*def)
                    .instantiate(generics, ctxt.tcx);

                let result_layout = ctxt.tcx.layout_of(signature.returns).unwrap();

                let mut param_tys = Vec::<ll::BasicMetadataTypeEnum<'ll>>::with_capacity(signature.params.len());
                for param in signature.params {
                    let layout = ctxt.tcx.layout_of(param.ty).unwrap();
                    match layout.repr {
                        layout::BackendRepr::Scalar(scalar) => { 
                            param_tys.push(scalar.llvm_type(ctxt).force_into());
                        }
                        layout::BackendRepr::ScalarPair(scalar1, scalar2) => {    
                            param_tys.push(scalar1.llvm_type(ctxt).force_into());
                            param_tys.push(scalar2.llvm_type(ctxt).force_into());
                        }
                        layout::BackendRepr::Memory => {
                            param_tys.push(ctxt.context.ptr_type(ll::AddressSpace::from(0)).into());
                        }
                    }
                }
                return match result_layout.repr {
                    layout::BackendRepr::Scalar(_) => {
                        let ret_ty: ll::BasicTypeEnum<'ll> = result_layout.llvm_type(ctxt).force_into();
                        ll::AnyTypeEnum::FunctionType(ret_ty.fn_type(&param_tys, false))
                    }
                    layout::BackendRepr::ScalarPair(scalar1, _) => {
                        // scalar1 is the result_ty, scalar2 passed as an out pointer argument
                        param_tys.push(ctxt.context.ptr_type(ll::AddressSpace::from(0)).into());
                        let ret_ty: ll::BasicTypeEnum<'ll> = scalar1.llvm_type(ctxt).force_into();
                        ll::AnyTypeEnum::FunctionType(ret_ty.fn_type(&param_tys, false))
                    }
                    layout::BackendRepr::Memory => {
                        if result_layout.size.in_bytes > 0 {
                            // memory values need to be passed passed as an out pointer argument

                            // FIXME: we should check how big the memory type is, (e.g. struct of 5
                            // bytes) maybe it still fits into a scalar (e.g. I64). So instead of using
                            // a pointer here, we could just cast it. This can only be done once we
                            // have better datastructes (e.g. a PassStyle) reducing the duplication
                            // in param deduction between here, function calling and param unwrapping
                            param_tys.push(ctxt.context.ptr_type(ll::AddressSpace::from(0)).into());
                        }
                        ll::AnyTypeEnum::FunctionType(ctxt.context.void_type().fn_type(&param_tys, false))
                    }
                };
            }
            Ty(TyKind::Int(..) | TyKind::Float(..) | TyKind::Char) =>
                panic!("should have been picked up by BackendRepr::Scalar and been handled"),
            Ty(TyKind::Err) => panic!("there it should be no error types in codegen pass"),
            _ => ()
        }

        match self.fields {
            layout::Fields::Scalar => unreachable!(),
            layout::Fields::Array { count, .. } => {
                let Ty(TyKind::Array(base_ty, _)) = self.ty else {
                    unreachable!()
                };
                let base_layout = ctxt.tcx.layout_of(*base_ty).unwrap();
                let base_ty: ll::BasicTypeEnum<'ll> = base_layout.llvm_type(ctxt).force_into();
                ll::AnyTypeEnum::ArrayType(base_ty.array_type(count as u32))
            }
            layout::Fields::Struct { ref fields } =>
                self.lower_fields(fields.iter_enumerated().map(|(f, o)| (f, *o)), ctxt)
        }
    }

    fn lower_fields<'ll>(&self, _field_offsets: impl Iterator<Item = (type_ir::FieldIdx, u64)>, ctxt: &CodegenCtxt<'ll, 'tcx>) -> ll::AnyTypeEnum<'ll> {
        let def;
        let field_tys = match self.ty {
            Ty(TyKind::String | TyKind::Slice(..)) => {
                def = None;
                let nuint = layout::Scalar::Int(type_ir::Integer::ISize.normalize(ctxt), false).llvm_type(ctxt)
                    .force_into();

                let mut fields = vec![];
                fields.push(ll::BasicTypeEnum::PointerType(ctxt.context.ptr_type(ll::AddressSpace::from(0)))); // void *data;
                fields.push(nuint);                                                                          // nuint count;
                fields
            }
            Ty(TyKind::DynamicArray(..)) => {
                def = None;
                let nuint = layout::Scalar::Int(type_ir::Integer::ISize.normalize(ctxt), false).llvm_type(ctxt).force_into();

                let mut fields = vec![];
                fields.push(ll::BasicTypeEnum::PointerType(ctxt.context.ptr_type(ll::AddressSpace::from(0)))); // void *items;
                fields.push(nuint);                                                                          // nuint count;
                fields.push(nuint);                                                                          // nuint capacity;
                fields
            }
            Ty(TyKind::Adt(AdtDef(AdtKind::Struct(strct)), generics)) => {
                def = Some(strct.def);
                strct.fields()
                    .map(|(_, data)| {
                        let ty = ctxt.tcx.type_of(data.def).instantiate(generics, ctxt.tcx);
                        let layout = ctxt.tcx.layout_of(ty).unwrap();
                        layout.llvm_type(ctxt).force_into()
                    })
                    .collect::<Vec<_>>()
            }
            Ty(TyKind::Adt(AdtDef(AdtKind::Union), _)) => todo!(),
            Ty(TyKind::Range(..)) => todo!(),
            else_ => panic!("{else_:?} is invalid here")
        };

        // TODO(once CSE and non-C structs are available): add padding fields to accomplish the
        // calculated offsets. For now they should be equal

        let strct;
        if let Some(def) = def {
            let ast::Node::Item(item) = ctxt.tcx.node_by_def_id(def) else { panic!("def should be struct"); };
            strct = ctxt.context.opaque_struct_type(item.get_name(ctxt.tcx).get());
            strct.set_body(&field_tys, false);
        } else {
            strct = ctxt.context.struct_type(&field_tys, false);
        }

        ll::AnyTypeEnum::StructType(strct)
    }
}

impl Scalar {
    fn llvm_type<'ll, 'tcx>(&self, ctxt: &CodegenCtxt<'ll, 'tcx>) -> ll::AnyTypeEnum<'ll> {
        let context = ctxt.context;
        match self {
            layout::Scalar::Int(int, _) => {
                let int_type = match int {
                    type_ir::Integer::I8 => context.i8_type(),
                    type_ir::Integer::I16 => context.i16_type(),
                    type_ir::Integer::I32 => context.i32_type(),
                    type_ir::Integer::I64 => context.i64_type(),
                    type_ir::Integer::ISize => {
                        let normalized = layout::Scalar::Int(int.normalize(ctxt), false);
                        return normalized.llvm_type(ctxt);
                    }
                };
                ll::AnyTypeEnum::IntType(int_type)
            }
            layout::Scalar::Float(float) => {
                let float_type = match float {
                    type_ir::Float::F32 => context.f32_type(),
                    type_ir::Float::F64 => context.f64_type(),
                };
                ll::AnyTypeEnum::FloatType(float_type)
            }
            layout::Scalar::Pointer =>
                ll::AnyTypeEnum::PointerType(context.ptr_type(ll::AddressSpace::from(0)))
        }
    }
}

// impl<'tcx> type_ir::Global<'tcx> {
//     fn get_name(&self, tcx: TyCtxt<'tcx>) -> symbol::Symbol {
//         match self {
//             type_ir::Global(type_ir::GlobalKind::Function { def, .. } | type_ir::GlobalKind::Static { def, .. }) => {
//                 let ast::Node::Item(item) = tcx.node_by_def_id(*def) else { unreachable!() };
//                 item.get_name(tcx)
//             }
//             type_ir::Global(type_ir::GlobalKind::EnumVariant { def }) => {
//                 let (_, variant) = tcx.enum_variant(*def);
//                 variant.symbol
//             }
//             type_ir::Global(type_ir::GlobalKind::Indirect { allocation, .. }) => {
//                 let id = allocation.as_ptr().addr();
//                 symbol::Symbol::intern(&format!("_clyialloc_{id:016x}"))
//             }
//         }
//     }
// 
//     fn is_function(&self) -> bool {
//         if let type_ir::Global(type_ir::GlobalKind::Function { .. }) = self {
//             return true;
//         }
//         false
//     }
// 
//     fn definition(&self) -> Option<ast::DefId> {
//         if let type_ir::Global(type_ir::GlobalKind::Function { def, .. } | type_ir::GlobalKind::Static { def, .. }) = self {
//             return Some(*def);
//         }
//         None
//     }
// 
//     fn args(&self) -> Option<&'tcx GenericArgs<'tcx>> {
//         if let type_ir::Global(type_ir::GlobalKind::Function { generics, .. }) = self {
//             return Some(generics);
//         }
//         None
//     }
// 
//     fn initializer(&self) -> Option<Const<'tcx>> {
//         if let type_ir::Global(type_ir::GlobalKind::Static { initializer, .. }) = self {
//             return Some(*initializer);
//         }
//         None
//     }
// 
//     fn ty(&self, tcx: TyCtxt<'tcx>) -> Ty<'tcx> {
//         match self {
//             type_ir::Global(type_ir::GlobalKind::Function { def, .. } | type_ir::GlobalKind::EnumVariant { def, .. } | type_ir::GlobalKind::Static { def, .. }) => tcx.type_of(*def),
//             type_ir::Global(type_ir::GlobalKind::Indirect { ty, .. }) => *ty
//         }
//     }
// }

impl<'tcx> ast::Item<'tcx> {
    fn get_name(&self, tcx: TyCtxt<'tcx>) -> symbol::Symbol {
        /*if let ast::ItemKind::Function(func) = self.kind {
            let header = &func.sig.header;
            if let Some(c_call) = header.c_call {
                if let Some((_, name)) = c_call.link_name {
                    return name;
                }
                return func.ident.symbol;
            }
            if let Some(_) = header.link {
                return func.ident.symbol;
            }
            if let Some(_) = header.compiler_intrinsic {
                panic!("intrinsics should not be handled like this");
            }
        }

        tcx.resolutions.mangled_names[&self.node_id]*/
        todo!()
    }
}

pub struct CodegenResults;

const LINKER: &'static str = r"C:\Program Files (x86)\Microsoft Visual Studio\2022\BuildTools\VC\Tools\MSVC\14.42.34433\bin\Hostx64\x64\link.exe";

const BASIC_ARGS: [&'static str; 9] = [
    r"-defaultlib:libcmt",
    r"-defaultlib:oldnames",
    r"-libpath:C:\Program Files (x86)\Microsoft Visual Studio\2022\BuildTools\VC\Tools\MSVC\14.42.34433\lib\x64",
    r"-libpath:C:\Program Files (x86)\Microsoft Visual Studio\2022\BuildTools\VC\Tools\MSVC\14.42.34433\atlmfc\lib\x64",
    r"-libpath:C:\Program Files (x86)\Windows Kits\10\Lib\10.0.22621.0\ucrt\x64",
    r"-libpath:C:\Program Files (x86)\Windows Kits\10\Lib\10.0.22621.0\um\x64",
    r"-libpath:C:\Program Files\LLVM\lib\clang\20\lib\windows",
    r"-nologo",
    r"helpers.o",
];

pub fn run_codegen(tcx: TyCtxt) -> CodegenResults {
    let arena = bumpalo::Bump::new();

    let entry = tcx.resolutions.entry.expect("program should have an entrypoint");

    let mut ctxt = CodegenCtxt::new(tcx, &arena);

    monomorphization::monomorph_items(tcx);


    ctxt.push_dependency(entry, None, None);

    for def in &tcx.resolutions.items {
        let node = tcx.node_by_def_id(*def);
        if let ast::Node::Item(ast::Item { kind: ast::ItemKind::Function(func), .. }) = node && func.sig.header.c_call.is_some() {
            ctxt.push_dependency(*def, None, None);
        }
    }

    ctxt.generate_code_bfs();

    let session = tcx.session;
    let machine = session.target.get_llvm_target_machine();

    let output = &session.output_dir;
    let mut opt_level = Some(session.config.opt_level);
    if opt_level == Some(OptimizationLevel::O0) {
        opt_level.take();
    }
    let passes = opt_level.map(|level| format!("default<{}>", level.as_str()));

    let mut modules = vec![];
    for (_, module) in ctxt.module_map.iter() {
        if let Some(ref passes) = passes {
            let result = module.run_passes(passes, machine, ll::PassBuilderOptions::create());
            if let Err(err) = result {
                eprintln!("ERROR: couldn't optimize module: {}: {}", module.get_name().to_bytes().escape_ascii(), err);
            }
        }
        if tcx.session.config.print_llvm_ir {
            module.print_to_stderr();
        }


        let mut path = output.clone();
        path.push(format!("{}.o", module.get_name().to_bytes().escape_ascii()));

        // TODO: properly report error
        machine.write_to_file(*module, ll::FileType::Object, &path)
            .unwrap();
        modules.push(path);
    }

    let mut linker = Command::new(LINKER);

    let mut out = OsString::new();
    write!(out, "-out:").unwrap();
    out.push(session.output_file.as_os_str());

    linker.arg(out);
    linker.args(BASIC_ARGS);
    linker.args(modules);

    linker.current_dir(&session.working_dir);

    linker.status()
        .expect("linker exited unsuccessfully");

    CodegenResults
}

mod ll {
    pub use inkwell::{
        context::Context,
        module::{Module, Linkage},
        builder::Builder,
        basic_block::BasicBlock,
        types::{AnyTypeEnum, BasicTypeEnum, BasicMetadataTypeEnum, IntType, FloatType, BasicType},
        values::{IntValue, FloatValue, FunctionValue, GlobalValue, ArrayValue, PointerValue, BasicValueEnum, BasicValue},
        targets::FileType,
        passes::PassBuilderOptions,
        AddressSpace,
        IntPredicate,
        FloatPredicate
    };
}

