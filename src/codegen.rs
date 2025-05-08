use std::{cell::RefCell, collections::VecDeque, ffi::OsString, hash::{BuildHasher, Hasher}, fmt::Write, process::Command};

use foldhash::quality::FixedState;
use index_vec::IndexVec;
use ll::{BasicType, AnyValue, BasicValue};
use hashbrown::{HashMap, HashSet, hash_map::Entry};

use crate::{analysis::intermediate::{self, Mutability, RegisterId}, context::{ModuleInfo, TyCtxt}, session::OptimizationLevel, syntax::ast, target::{DataLayoutExt, TargetDataLayout}, type_ir::{self, AdtDef, AdtKind, Const, ConstKind, Scalar, Ty, TyKind, TyLayoutTuple}};
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
     align: type_ir::Align,
}

#[derive(Debug, Clone, Copy)]
enum ValueKind<'ll> {
     Ref(Place<'ll>),
     Immediate(ll::AnyValueEnum<'ll>),
     Pair(ll::AnyValueEnum<'ll>, ll::AnyValueEnum<'ll>),
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
            ValueKind::Pair(..) =>
                panic!("cannot deref ValueKimd::Pair: pointers always fit into immediates"),
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

                let type_ir::BackendRepr::ScalarPair(scalar1, scalar2) = self.layout.repr else {
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
            type_ir::BackendRepr::Scalar(_) => {
                let llvm_ty: ll::BasicTypeEnum<'ll> = layout.llvm_type(self.cctxt).force_into();
                let value = ensure!(self.builder.build_load(llvm_ty, place.value, ""));
                value.as_instruction_value()
                    .unwrap()
                    .set_alignment(place.align.in_bytes() as u32)
                    .unwrap();
                Value {
                    kind: ValueKind::Immediate(value.as_any_value_enum()),
                    layout
                }
            }
            type_ir::BackendRepr::ScalarPair(scalar1, scalar2) => {
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
                    kind: ValueKind::Pair(value1.as_any_value_enum(), value2.as_any_value_enum()),
                    layout
                }
            }
            type_ir::BackendRepr::Memory => {
                Value {
                    kind: ValueKind::Ref(place),
                    layout
                }
            }
        }
    }

    fn alloca_place(&mut self, layout: TyLayoutTuple<'tcx>) -> Place<'ll> {
        let align = layout.align;

        let array_ty = self.cctxt.context.i8_type()
            .array_type(layout.size.in_bytes as u32);

        let pointer = ensure!(self.builder.build_alloca(array_ty, ""));
        pointer
            .as_instruction()
            .unwrap()
            .set_alignment(align.in_bytes() as u32)
            .unwrap();
        
        Place { value: pointer, align }
    }

    fn lower_place(&mut self, ir_place: intermediate::Place<'tcx>) -> (Place<'ll>, TyLayoutTuple<'tcx>) {
        use intermediate::Place::*;
        let (Register(target) | Deref(target) | Field { target, .. } | Index { target, .. }) = ir_place else {
            panic!("Place::None is not supported here");
        };
        let (cg_place, ty) = match self.reg_translations[target] {
            LocalKind::Place { place, layout: ty } => (place, ty),
            LocalKind::Value(value) => {
                let Deref(..) = ir_place else {
                    panic!("only Place::Deref makes a LocalKind::Value here");
                };
                return value.deref(self);
            }
            LocalKind::Dangling => panic!("tried to resolve a LocalKind::Dangling")
        };
        match ir_place {
            Deref(_) => {
                let value = self.load_value(cg_place, ty);
                value.deref(self)
            },
            Register(_) => (cg_place, ty),
            Field { field, ty: res_ty, .. } => {
                let llvm_ty: ll::BasicTypeEnum<'ll> = ty.llvm_type(self.cctxt)
                    .force_into();

                let value = ensure!(self.builder.build_struct_gep(llvm_ty, cg_place.value, field.raw(), ""));
                let res_layout = self.tcx.layout_of(res_ty).unwrap();
                (Place { value, align: res_layout.align }, res_layout)
            }
            Index { idx, .. } => {
                let element = match ty.ty {
                    Ty(TyKind::Array(element, ..) | TyKind::Slice(element) | TyKind::DynamicArray(element) | TyKind::Refrence(element)) => *element,
                    Ty(TyKind::String) => self.tcx.basic_types.byte,
                    _ => panic!("Can't index {ty:?}"),
                };
                let element = self.tcx.layout_of(element).unwrap();
                let ptr = match ty.ty {
                    Ty(TyKind::DynamicArray(..) | TyKind::Slice(..) | TyKind::String) => {
                        let fictional_ty = self.tcx.layout_of(Ty::new_refrence(self.tcx, element.ty)).unwrap();
                        let Value { kind: ValueKind::Immediate(value), .. } = self.load_value(cg_place, fictional_ty) else {
                            panic!("Place::Index: pointers always fit into immediates");
                        };
                        value.force_into()
                    }
                    _ => cg_place.value
                };
                let llvm_element: ll::BasicTypeEnum<'ll> = element.llvm_type(self.cctxt).force_into();
                let Value { kind: ValueKind::Immediate(idx), .. } = self.lower_operand(idx) else {
                    panic!("ValueKinds other than ValueKind::Immediate is not valid on Place::Index");
                };
                let idx: ll::IntValue<'ll> = idx.force_into();

                let value = ensure!(unsafe { self.builder.build_in_bounds_gep(llvm_element, ptr, &[idx], "") });
                (Place {
                    value,
                    align: element.align
                }, element)
            }
            None => unreachable!()
        }
    }

    fn lower_const_value(&mut self, cnst: Const<'tcx>) -> Value<'ll, 'tcx> {
        // FIXME: this should be extensively handled by an even better const downcast_unsized
        // system instead of this match here (downcast to `LLVMConstValueConversion` or a better name
        // for this trait)
        match cnst {
            Const(ConstKind::Definition(def)) => {
                let node = self.tcx.node_by_def_id(*def);
                let ll_value = if let ast::Node::Item(ast::Item { kind: ast::ItemKind::Function(..), .. }) = node {
                    let function = self.cctxt.push_dependency(*def);
                    ll::AnyValueEnum::FunctionValue(function)
                } else {
                    todo!("global items like static variables, etc")
                };
                let ty = self.tcx.type_of(*def);
                let layout = self.tcx.layout_of(ty).unwrap();
                Value {
                    kind: ValueKind::Immediate(ll_value),
                    layout
                }
            }
            Const(ConstKind::Value(value)) => {
                let layout = self.tcx.layout_of(value.ty).unwrap();
                let ll_ty = layout.llvm_type(self.cctxt);
                if let ll::AnyTypeEnum::IntType(int_ty) = ll_ty {
                    // should take care of Bool, Char and any Integer
                    let value = value.downcast_unsized::<dyn num_traits::ToPrimitive>()
                        .unwrap()
                        .to_i128()
                        .unwrap();
                    let value = ll::AnyValueEnum::IntValue(int_ty.const_int(value as u64, false));
                    return Value {
                        kind: ValueKind::Immediate(value),
                        layout
                    };
                }
                if let Ty(TyKind::String) = layout.ty {
                    let string_data = value.as_bytes();
                    let nuint_layout = self.tcx.layout_of(self.tcx.basic_types.nuint).unwrap();


                    let nuint_type = nuint_layout.llvm_type(self.cctxt).into_int_type();

                    let data = self.cctxt.allocate_string_data(self.module, string_data);
                    let size = nuint_type.const_int(string_data.len() as u64, false);

                    return Value {
                        kind: ValueKind::Pair(data.as_any_value_enum(), size.as_any_value_enum()),
                        layout,
                    };
                }

                todo!("other kinds of constant values are currently unsupported")
            }
            Const(ConstKind::Err | ConstKind::Infer) =>
                panic!("ConstKind::Err, ConstKind::Infer are invalid at Codegen phase")
        }
    }

    fn lower_operand(&mut self, operand: intermediate::Operand<'tcx>) -> Value<'ll, 'tcx> {
        match operand {
            intermediate::Operand::Copy(reg) => {
                match self.reg_translations[reg] {
                    LocalKind::Value(value) => value,
                    LocalKind::Place { place, layout: ty } => self.load_value(place, ty),
                    LocalKind::Dangling => panic!("tried to resolve a LocalKind::Dangling")
                }
            },
            intermediate::Operand::Const(cnst) => self.lower_const_value(cnst),
        }
    }

    fn visit_statement(&mut self, statement: &'tcx intermediate::Statement<'tcx>) {
        use intermediate::Place;
        let deferred = match statement.place {
            Place::Register(reg) if let LocalKind::Dangling = self.reg_translations[reg] =>
                DeferredStorage::Initialize(reg),
            Place::None => DeferredStorage::None,
            _ => {
                let (cg_place, ty) = self.lower_place(statement.place);
                DeferredStorage::Place { place: cg_place, layout: ty }
            }
        };

        match statement.rhs {
            intermediate::RValue::Ref(ir_place) => {
                let (cg_place, mut layout) = self.lower_place(ir_place);
                layout = self.tcx.layout_of(Ty::new_refrence(self.tcx, layout.ty)).unwrap();
                let value = Value {
                    kind: ValueKind::Immediate(cg_place.value.as_any_value_enum()),
                    layout,
                };
                deferred.store_or_init(value, self);
            }
            intermediate::RValue::Read(ir_place) => {
                let (cg_place, ty) = self.lower_place(ir_place);
                let value = self.load_value(cg_place, ty);
                deferred.store_or_init(value, self);
            }
            intermediate::RValue::Const(cnst) => {
                let value = self.lower_const_value(cnst);
                deferred.store_or_init(value, self);
            }
            intermediate::RValue::Call { callee, ref args } => {
                let Value { kind: ValueKind::Immediate(function), layout } = self.lower_operand(callee) else {
                    panic!("function value needs to be ValueKind::Immediate");
                };
                let Ty(TyKind::Function(fndef)) = layout.ty else {
                    panic!("{:?} is not callable", layout.ty);
                };
                let sig = self.tcx.fn_sig(*fndef);

                let mut arguments = vec![];
                for (idx, param) in sig.params.iter().enumerate() {
                    let value = args[idx];
                    let value = self.lower_operand(value.operand);

                    let layout = self.tcx.layout_of(param.ty).unwrap();
                    match (value.kind, layout.repr) {
                        (ValueKind::Immediate(value), type_ir::BackendRepr::Scalar(..)) =>
                            arguments.push(value.force_into()),
                        (ValueKind::Pair(value1, value2), type_ir::BackendRepr::ScalarPair(..)) => {    
                            arguments.push(value1.force_into());
                            arguments.push(value2.force_into());
                        }
                        (ValueKind::Ref(place), type_ir::BackendRepr::Memory) => {
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

                let result_ty = match layout.ty {
                    Ty(TyKind::Function(def)) => {
                        let sig = self.tcx.fn_sig(*def);
                        sig.returns
                    },
                    _ => panic!("{:?} is not callable", layout.ty)
                };
                let result_layout = self.tcx.layout_of(result_ty).unwrap();

                let mut ll_result = None;
                let mut mem_argload = None;
                match result_layout.repr {
                    type_ir::BackendRepr::Scalar(..) =>
                        ll_result = Some(()),
                    type_ir::BackendRepr::ScalarPair(_, scalar2) => {
                        ll_result = Some(());

                        let arg_layout = self.tcx.layout_of(scalar2.get_type(self.tcx)).unwrap();
                        let tmp = self.alloca_place(arg_layout);
                        arguments.push(tmp.value.into());

                        mem_argload = Some((tmp, arg_layout));
                    }
                    type_ir::BackendRepr::Memory => {
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

                let result = ensure!(self.builder.build_call(function.into_function_value(), &arguments, ""));
                let result = ll_result.map(|()| result);

                let value = match (result, mem_argload) {
                    (Some(result), None) => { // scalar return
                        Value {
                            kind: ValueKind::Immediate(result.as_any_value_enum()),
                            layout: result_layout
                        }
                    }
                    (Some(result), Some((sideload, layout))) => { // scalar pair return
                        let Value { kind: ValueKind::Immediate(llval), .. } = self.load_value(sideload, layout) else {
                            unreachable!()
                        };
                        Value {
                            kind: ValueKind::Pair(result.as_any_value_enum(), llval),
                            layout
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
                let Value { kind: ValueKind::Immediate(llvm_value), layout: val_layout } = self.lower_operand(value) else {
                    panic!("RValue::BinaryOp is only valid for ValueKind::Immediate");
                };
                let res = match (val_layout.ty, res_ty) {
                    (Ty(TyKind::Int(..)), Ty(TyKind::Int(_, signed))) => {
                        let int_value: ll::IntValue<'ll> = llvm_value.force_into();
                        let int_type: ll::IntType<'ll> = result_layout.llvm_type(self.cctxt)
                            .force_into();
                        ensure!(self.builder.build_int_cast_sign_flag(int_value, int_type, *signed, ""))
                            .as_any_value_enum()
                    }
                    (Ty(TyKind::Float(..)), Ty(TyKind::Float(..))) => {
                        let float_value: ll::FloatValue<'ll> = llvm_value.force_into();
                        let float_type: ll::FloatType<'ll> = result_layout.llvm_type(self.cctxt)
                            .force_into();
                        ensure!(self.builder.build_float_cast(float_value, float_type, ""))
                            .as_any_value_enum()
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
                        res.as_any_value_enum()
                    }
                    (Ty(TyKind::Int(type_ir::Integer::I8, false)), Ty(TyKind::Bool)) => llvm_value,
                    (Ty(TyKind::Int(type_ir::Integer::I32, false)), Ty(TyKind::Char)) => llvm_value,
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
                    kind: ValueKind::Immediate(res.as_any_value_enum()),
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
                        res.as_any_value_enum()
                    }
                    Ty(TyKind::Float(_)) => {
                        let value: ll::FloatValue<'ll> = value.force_into();
                        let res = ensure!(self.builder.build_float_neg(value, ""));
                        res.as_any_value_enum()
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
                    Ty(TyKind::Array(element, count)) => {
                        let element_layout = self.tcx.layout_of(*element).unwrap();
                        let count = count.downcast_unsized::<dyn num_traits::ToPrimitive>()
                            .unwrap()
                            .to_u64()
                            .unwrap();
                        if initializers.len() == 1 {
                            let default = self.lower_operand(initializers[0].1.operand);
                            let id = (statement as *const intermediate::Statement<'tcx>).addr() as u16;
                            self.default_initialize_array(dest, element_layout, default, count, id);
                        } else {
                            debug_assert!(initializers.len() as u64 == count);
                            self.initialize_with_initializers(dest, element_layout, initializers, false);
                        }
                    }
                    Ty(TyKind::Adt(AdtDef(AdtKind::Struct(..)))) => {
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
                let Ty(TyKind::Adt(AdtDef(AdtKind::Struct(strct)))) = layout.ty else {
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
                    type_ir::BackendRepr::Scalar(_) => {
                        let value = self.lower_operand(value);
                        let Value { kind: ValueKind::Immediate(value), .. } = value else {
                            panic!("ValueKind should match BackendRepr");
                        };
                        let value: ll::BasicValueEnum<'ll> = value.force_into();
                        ensure!(self.builder.build_return(Some(&value)));
                    }
                    type_ir::BackendRepr::ScalarPair(_scalar1, scalar2) => {

                        let value = self.lower_operand(value);
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
                    type_ir::BackendRepr::Memory => {
                        if layout.size.in_bytes > 0 {
                            let value = self.lower_operand(value);
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
        let mut placebounds = HashSet::new();
        for block in &body.basic_blocks {
            for statement in &block.statements {
                
                if let intermediate::RValue::Read(place) | intermediate::RValue::Ref(place) = statement.rhs &&
                    let Some(reg) = get_reg(place) {
                    placebounds.insert(reg);
                }
            }
        }

        return placebounds;

        fn get_reg(place: intermediate::Place) -> Option<RegisterId> {
            use intermediate::Place::*;
            if let Register(target) | Field { target, .. } | Index { target, .. } = place {
                return Some(target);
            }
            Option::None
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
                type_ir::BackendRepr::Scalar(..) => {
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
                type_ir::BackendRepr::ScalarPair(..) => {
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
                type_ir::BackendRepr::Memory => {
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
    string_data_map: HashMap<&'ll [u8], ll::PointerValue<'ll>>,
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
            string_data_map: HashMap::new(),
            type_translation_cache: RefCell::new(HashMap::new()),
            depedency_queue: VecDeque::new(),
            target_data_layout: *tcx.data_layout()
        }
    }

    fn allocate_string_data(&mut self, module: &'ll ll::Module<'ll>, string_data: &[u8]) -> ll::PointerValue<'ll> {
        if let Some(value) = self.string_data_map.get(string_data) {
            return *value;
        }

        let byte_type = self.tcx.layout_of(self.tcx.basic_types.byte)
            .unwrap()
            .llvm_type(self).into_int_type();

        let mut values = Vec::with_capacity(string_data.len());
        for byte in string_data {
            values.push(byte_type.const_int(*byte as u64, false));
        }
        let llvm_array = byte_type.const_array(&values);

        let string_global = module.add_global(byte_type.array_type(values.len() as u32), None, &format!("string_data_{:x}", hash_data(string_data)));
        string_global.set_initializer(&llvm_array);

        let value = string_global.as_pointer_value();
        self.string_data_map.insert(self.arena.alloc_slice_copy(string_data), value);
        value
    }

    fn push_dependency(&mut self, def: ast::DefId) -> ll::FunctionValue<'ll> {
        if let Some(DependencyData { value, .. }) = self.dependency_map.get(&def) {
            return *value;
        }

        let node = self.tcx.node_by_def_id(def);
        let ast::Node::Item(ast::Item { kind: ast::ItemKind::Function(func), .. }) = node else {
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
        let layout = self.tcx.layout_of(ty).unwrap();

        let mangled_name = self.tcx.resolutions.mangled_names[&node.node_id()];
        let function = module
            .add_function(
                mangled_name.get(),
                layout.llvm_type(self).into_function_type(),
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

const HASH_STATE: FixedState = FixedState::with_seed(0xd1310ba698dfb5ac);

fn hash_data(data: &[u8]) -> u64 {
    let mut hasher = HASH_STATE.build_hasher();
    hasher.write(data);
    hasher.finish()
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
            type_ir::BackendRepr::Scalar(..) => true,
            type_ir::BackendRepr::ScalarPair(..) | type_ir::BackendRepr::Memory => false,
        }
    }

    fn lower_type_and_layout<'ll>(&self, ctxt: &CodegenCtxt<'ll, 'tcx>) -> ll::AnyTypeEnum<'ll> {
        if let type_ir::BackendRepr::Scalar(scalar) = self.repr && !matches!(self.ty, Ty(TyKind::Bool)){
            return scalar.llvm_type(ctxt);
        }

        match self.ty {
            Ty(TyKind::Bool) => 
                return ll::AnyTypeEnum::IntType(ctxt.context.bool_type()),
            // TODO: is never == void ok here?
            Ty(TyKind::Void | TyKind::Never) => 
                return ll::AnyTypeEnum::VoidType(ctxt.context.void_type()),
            Ty(TyKind::Function(def)) => {
                let signature = ctxt.tcx.fn_sig(*def);

                let result_layout = ctxt.tcx.layout_of(signature.returns).unwrap();

                let mut param_tys = Vec::<ll::BasicMetadataTypeEnum<'ll>>::with_capacity(signature.params.len());
                for param in signature.params {
                    let layout = ctxt.tcx.layout_of(param.ty).unwrap();
                    match layout.repr {
                        type_ir::BackendRepr::Scalar(scalar) => { 
                            param_tys.push(scalar.llvm_type(ctxt).force_into());
                        }
                        type_ir::BackendRepr::ScalarPair(scalar1, scalar2) => {    
                            param_tys.push(scalar1.llvm_type(ctxt).force_into());
                            param_tys.push(scalar2.llvm_type(ctxt).force_into());
                        }
                        type_ir::BackendRepr::Memory => {
                            param_tys.push(ctxt.context.ptr_type(ll::AddressSpace::from(0)).into());
                        }
                    }
                }
                return match result_layout.repr {
                    type_ir::BackendRepr::Scalar(_) => {
                        let ret_ty: ll::BasicTypeEnum<'ll> = result_layout.llvm_type(ctxt).force_into();
                        ll::AnyTypeEnum::FunctionType(ret_ty.fn_type(&param_tys, false))
                    }
                    type_ir::BackendRepr::ScalarPair(scalar1, _) => {
                        // scalar1 is the result_ty, scalar2 passed as an out pointer argument
                        param_tys.push(ctxt.context.ptr_type(ll::AddressSpace::from(0)).into());
                        let ret_ty: ll::BasicTypeEnum<'ll> = scalar1.llvm_type(ctxt).force_into();
                        ll::AnyTypeEnum::FunctionType(ret_ty.fn_type(&param_tys, false))
                    }
                    type_ir::BackendRepr::Memory => {
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
            type_ir::Fields::Scalar => unreachable!(),
            type_ir::Fields::Array { count, .. } => {
                let Ty(TyKind::Array(base_ty, _)) = self.ty else {
                    unreachable!()
                };
                let base_layout = ctxt.tcx.layout_of(*base_ty).unwrap();
                let base_ty: ll::BasicTypeEnum<'ll> = base_layout.llvm_type(ctxt).force_into();
                ll::AnyTypeEnum::ArrayType(base_ty.array_type(count as u32))
            }
            type_ir::Fields::Struct { ref fields } =>
                self.lower_fields(fields.iter_enumerated().map(|(f, o)| (f, *o)), ctxt)
        }
    }

    fn lower_fields<'ll>(&self, _field_offsets: impl Iterator<Item = (type_ir::FieldIdx, u64)>, ctxt: &CodegenCtxt<'ll, 'tcx>) -> ll::AnyTypeEnum<'ll> {
        let def;
        let field_tys = match self.ty {
            Ty(TyKind::String | TyKind::Slice(..)) => {
                def = None;
                let nuint = type_ir::Scalar::Int(type_ir::Integer::ISize.normalize(ctxt), false).llvm_type(ctxt)
                    .force_into();

                let mut fields = vec![];
                fields.push(ll::BasicTypeEnum::PointerType(ctxt.context.ptr_type(ll::AddressSpace::from(0)))); // void *data;
                fields.push(nuint);                                                                          // nuint count;
                fields
            }
            Ty(TyKind::DynamicArray(..)) => {
                def = None;
                let nuint = type_ir::Scalar::Int(type_ir::Integer::ISize.normalize(ctxt), false).llvm_type(ctxt).force_into();

                let mut fields = vec![];
                fields.push(ll::BasicTypeEnum::PointerType(ctxt.context.ptr_type(ll::AddressSpace::from(0)))); // void *items;
                fields.push(nuint);                                                                          // nuint count;
                fields.push(nuint);                                                                          // nuint capacity;
                fields
            }
            Ty(TyKind::Adt(AdtDef(AdtKind::Struct(strct)))) => {
                def = Some(strct.def);
                strct.fields()
                    .map(|(_, data)| {
                        let ty = ctxt.tcx.type_of(data.def);
                        let layout = ctxt.tcx.layout_of(ty).unwrap();
                        layout.llvm_type(ctxt).force_into()
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
        if let Some(def) = def {
            let node_id = ctxt.tcx.resolutions.declarations[def].node;
            let mangled_name = ctxt.tcx.resolutions.mangled_names[&node_id];
            strct = ctxt.context.opaque_struct_type(mangled_name.get());
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
            type_ir::Scalar::Int(int, _) => {
                let int_type = match int {
                    type_ir::Integer::I8 => context.i8_type(),
                    type_ir::Integer::I16 => context.i16_type(),
                    type_ir::Integer::I32 => context.i32_type(),
                    type_ir::Integer::I64 => context.i64_type(),
                    type_ir::Integer::ISize => {
                        let normalized = type_ir::Scalar::Int(int.normalize(ctxt), false);
                        return normalized.llvm_type(ctxt);
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
    r"bootstrap.o"
];

pub fn run_codegen(tcx: TyCtxt) -> CodegenResults {
    let arena = bumpalo::Bump::new();

    let entry = tcx.resolutions.entry.expect("program should have an entrypoint");

    let mut ctxt = CodegenCtxt::new(tcx, &arena);
    ctxt.push_dependency(entry);

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
                eprintln!("couldn't optimize module: {}: {}", module.get_name().to_bytes().escape_ascii(), err);
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
        values::{IntValue, FloatValue, FunctionValue, AnyValueEnum, PointerValue, BasicValueEnum, BasicValue, AnyValue},
        targets::FileType,
        passes::PassBuilderOptions,
        AddressSpace,
        IntPredicate,
        FloatPredicate
    };
}

