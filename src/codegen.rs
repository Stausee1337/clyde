use std::{cell::RefCell, collections::VecDeque, ffi::OsString, hash::{BuildHasher, Hasher}, fmt::Write, process::Command};

use foldhash::quality::FixedState;
use index_vec::IndexVec;
use ll::{BasicType, AnyValue, BasicValue};
use hashbrown::{HashMap, HashSet, hash_map::Entry};

use crate::{analysis::intermediate::{self, Mutability, RegisterId}, context::TyCtxt, session::OptimizationLevel, syntax::ast, target::{DataLayoutExt, TargetDataLayout}, type_ir::{self, AdtDef, AdtKind, Const, ConstKind, Ty, TyKind, TypeLayout}};
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
    ty: Ty<'tcx>
}

impl<'ll, 'tcx> Value<'ll, 'tcx> {
    fn deref<'a>(&self, builder: &mut CodeBuilder<'a, 'll, 'tcx>) -> (Place<'ll>, Ty<'tcx>){
        match self.kind {
            ValueKind::Immediate(value) => {
                let Ty(TyKind::Refrence(inner)) = self.ty else {
                    panic!("Cannot deref {:?}", self.ty);
                };
                let layout = builder.generator.tcx.layout_of(*inner)
                    .ok()
                    .unwrap();
                let place = Place {
                    value: value.into_pointer_value(),
                    align: layout.align.abi
                };
                (place, *inner)
            }
            ValueKind::Pair(..) =>
                panic!("cannot deref ValueKimd::Pair: pointers always fit into immediates"),
            ValueKind::Ref(..) =>
                panic!("cannot deref ValueKind::Ref:  pointers always fit into immediates")
        }
    }

    fn store<'a>(&self, 
        dest: Place<'ll>,
        _ty: Ty<'tcx>,
        builder: &mut CodeBuilder<'a, 'll, 'tcx>
    ) {
        debug_assert_eq!(_ty, self.ty, "why shouldn't that be the case?");
        match self.kind {
            ValueKind::Immediate(value) => {
                let value: ll::BasicValueEnum<'ll> = value.try_into().unwrap();
                let instruction = ensure!(builder.builder.build_store(dest.value, value));
                instruction.set_alignment(dest.align.in_bytes() as u32)
                    .unwrap();
            }
            ValueKind::Pair(value1, value2) => {
                let value1: ll::BasicValueEnum<'ll> = value1.try_into().unwrap();
                let value2: ll::BasicValueEnum<'ll> = value2.try_into().unwrap();

                let mut ptr = dest.value;

                let layout = builder.generator.tcx.layout_of(self.ty)
                    .ok()
                    .unwrap();

                let type_ir::BackendRepr::ScalarPair(scalar1, scalar2) = layout.repr else {
                    panic!("ValueKind should match BackendRepr");
                };

                let instruction = ensure!(builder.builder.build_store(ptr, value1));
                instruction.set_alignment(dest.align.in_bytes() as u32)
                    .unwrap();


                let align = scalar2.align(builder.generator).abi;
                let offset = scalar1.size(builder.generator).align_up(align);
                let offset = builder.generator.context.i32_type().const_int(offset, false);

                ptr = unsafe { 
                    ensure!(builder.builder.build_in_bounds_gep(
                        builder.generator.context.i8_type(),
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
                let layout = builder.generator.tcx.layout_of(self.ty)
                    .ok()
                    .unwrap();
                if layout.is_llvm_immediate() {
                    let value = builder.load_value(place, self.ty);
                    value.store(dest, self.ty, builder);
                } else if layout.size.in_bytes > 0 {
                    let llvm_i64 = builder.generator.context.i64_type();
                    ensure!(builder.builder.build_memcpy(
                        dest.value, dest.align.in_bytes() as u32,
                        place.value, place.align.in_bytes() as u32,
                        llvm_i64.const_int(layout.size.in_bytes, false)));
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
         ty: Ty<'tcx>
     },
     #[default]
     Dangling
}

enum DeferredStorage<'ll, 'tcx> {
    Place {
         place: Place<'ll>,
         ty: Ty<'tcx>, 
    },
    Initialize(intermediate::RegisterId),
    None,
}

impl<'ll, 'tcx> DeferredStorage<'ll, 'tcx> {
    fn store_or_init<'a>(self, value: Value<'ll, 'tcx>, builder: &mut CodeBuilder<'a, 'll, 'tcx>) {
        match self {
            DeferredStorage::Place { place, ty } =>
                value.store(place, ty, builder),
            DeferredStorage::Initialize(reg) => {
                let local = &mut builder.reg_translations[reg];
                assert!(matches!(local, LocalKind::Dangling));
                *local = LocalKind::Value(value);
            }
            DeferredStorage::None => ()
        }
    }
}

struct CodeBuilder<'a, 'll, 'tcx> {
    module: &'ll ll::Module<'ll>,
    builder: ll::Builder<'ll>,
    function: ll::FunctionValue<'ll>,
    generator: &'a mut CodegenCtxt<'ll, 'tcx>,
    reg_translations: IndexVec<intermediate::RegisterId, LocalKind<'ll, 'tcx>>,
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
            reg_translations: IndexVec::new(),
            block_translations: IndexVec::new()
        }
    }

    fn load_value(&mut self, place: Place<'ll>, ty: Ty<'tcx>) -> Value<'ll, 'tcx> {
        let layout = self.generator.tcx.layout_of(ty)
            .ok()
            .unwrap();
        match layout.repr {
            type_ir::BackendRepr::Scalar(_) => {
                let llvm_ty: ll::BasicTypeEnum<'ll> = ty.llvm_type(self.generator)
                    .try_into()
                    .unwrap();
                let value = ensure!(self.builder.build_load(llvm_ty, place.value, ""));
                value.as_instruction_value()
                    .unwrap()
                    .set_alignment(place.align.in_bytes() as u32)
                    .unwrap();
                Value {
                    kind: ValueKind::Immediate(value.as_any_value_enum()),
                    ty
                }
            }
            type_ir::BackendRepr::ScalarPair(scalar1, scalar2) => {
                let llvm_ty: ll::BasicTypeEnum<'ll> = llvm_lower_scalar(scalar1, self.generator)
                    .try_into()
                    .unwrap();

                let mut ptr = place.value;

                let value1 = ensure!(self.builder.build_load(llvm_ty, ptr, ""));
                value1.as_instruction_value()
                    .unwrap()
                    .set_alignment(place.align.in_bytes() as u32)
                    .unwrap();

                let align = scalar2.align(self.generator).abi;
                let offset = scalar1.size(self.generator).align_up(align);
                let offset = self.generator.context.i32_type().const_int(offset, false);

                ptr = unsafe {
                    ensure!(self.builder.build_in_bounds_gep(
                        self.generator.context.i8_type(),
                        ptr,
                        &[offset],
                        ""
                    ))
                };

                let llvm_ty: ll::BasicTypeEnum<'ll> = llvm_lower_scalar(scalar2, self.generator)
                    .try_into()
                    .unwrap();

                let value2 = ensure!(self.builder.build_load(llvm_ty, ptr, ""));
                value2.as_instruction_value()
                    .unwrap()
                    .set_alignment(place.align.in_bytes() as u32)
                    .unwrap();

                Value {
                    kind: ValueKind::Pair(value1.as_any_value_enum(), value2.as_any_value_enum()),
                    ty
                }
            }
            type_ir::BackendRepr::Memory => {
                Value {
                    kind: ValueKind::Ref(place),
                    ty
                }
            }
        }
    }

    fn alloca_place(&mut self, ty: Ty<'tcx>) -> Place<'ll> {
        let layout = self.generator.tcx.layout_of(ty).ok().unwrap();
        let align = layout.align.abi;

        let array_ty = self.generator.context.i8_type()
            .array_type(layout.size.in_bytes as u32);

        let pointer = ensure!(self.builder.build_alloca(array_ty, ""));
        pointer
            .as_instruction()
            .unwrap()
            .set_alignment(align.in_bytes() as u32)
            .unwrap();
        
        Place { value: pointer, align }
    }

    fn lower_place(&mut self, ir_place: intermediate::Place<'tcx>) -> (Place<'ll>, Ty<'tcx>) {
        use intermediate::Place::*;
        let (Register(target) | Deref(target) | Field { target, .. } | Index { target, .. }) = ir_place else {
            panic!("Place::None is not supported here");
        };
        let (cg_place, ty) = match self.reg_translations[target] {
            LocalKind::Place { place, ty } => (place, ty),
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
                let llvm_ty: ll::BasicTypeEnum<'ll> = ty.llvm_type(self.generator)
                    .try_into()
                    .unwrap();

                let value = ensure!(self.builder.build_struct_gep(llvm_ty, cg_place.value, field.raw(), ""));
                let res_layout = self.generator.tcx.layout_of(res_ty)
                    .ok()
                    .unwrap();
                (Place { value, align: res_layout.align.abi }, res_ty)
            }
            Index { idx, .. } => {
                let Ty(TyKind::Array(element, ..) | TyKind::Slice(element) | TyKind::DynamicArray(element) | TyKind::Refrence(element)) = ty else {
                    panic!("Can't index {ty:?}");
                };
                let element: ll::BasicTypeEnum<'ll> = element.llvm_type(self.generator).force_into();
                let Value { kind: ValueKind::Immediate(idx), .. } = self.lower_operand(idx) else {
                    panic!("ValueKinds other than ValueKind::Immediate is not valid on Place::Index");
                };
                let idx: ll::IntValue<'ll> = idx.force_into();

                ensure!(unsafe { self.builder.build_in_bounds_gep(element, cg_place.value, &[idx], "") });
                todo!("Place::Index")
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
                let node = self.generator.tcx.node_by_def_id(*def);
                let ll_value = if let ast::Node::Item(ast::Item { kind: ast::ItemKind::Function(..), .. }) = node {
                    let function = self.generator.push_dependency(*def);
                    ll::AnyValueEnum::FunctionValue(function)
                } else {
                    todo!("global items like static variables, etc")
                };
                let ty = self.generator.tcx.type_of(*def);
                Value {
                    kind: ValueKind::Immediate(ll_value),
                    ty
                }
            }
            Const(ConstKind::Value(value)) => {
                let ty = value.ty;
                let ll_ty = ty.llvm_type(self.generator);
                if let ll::AnyTypeEnum::IntType(int_ty) = ll_ty {
                    // should take care of Bool, Char and any Integer
                    let value = value.downcast_unsized::<dyn num_traits::ToPrimitive>()
                        .unwrap()
                        .to_i128()
                        .unwrap();
                    let value = ll::AnyValueEnum::IntValue(int_ty.const_int(value as u64, false));
                    return Value {
                        kind: ValueKind::Immediate(value),
                        ty,
                    };
                }
                if let Ty(TyKind::String) = ty {
                    let string_data = value.as_bytes();


                    let nuint_type = self.generator.tcx.basic_types.nuint.llvm_type(self.generator).into_int_type();

                    let data = self.generator.allocate_string_data(self.module, string_data);
                    let size = nuint_type.const_int(string_data.len() as u64, false);

                    return Value {
                        kind: ValueKind::Pair(data.as_any_value_enum(), size.as_any_value_enum()),
                        ty,
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
                    LocalKind::Place { place, ty } => self.load_value(place, ty),
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
                DeferredStorage::Place { place: cg_place, ty }
            }
        };

        match statement.rhs {
            intermediate::RValue::Ref(ir_place) => {
                let (cg_place, mut ty) = self.lower_place(ir_place);
                ty = Ty::new_refrence(self.generator.tcx, ty);
                let value = Value {
                    kind: ValueKind::Immediate(cg_place.value.as_any_value_enum()),
                    ty,
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
                let Value { kind: ValueKind::Immediate(function), ty } = self.lower_operand(callee) else {
                    panic!("function value needs to be ValueKind::Immediate");
                };
                let Ty(TyKind::Function(fndef)) = ty else {
                    panic!("{ty:?} is not callable");
                };
                let sig = self.generator.tcx.fn_sig(*fndef);

                let mut arguments = vec![];
                for (idx, param) in sig.params.iter().enumerate() {
                    let value = args[idx];
                    let value = self.lower_operand(value.operand);

                    let layout = self.generator.tcx.layout_of(param.ty).ok().unwrap();
                    match (value.kind, layout.repr) {
                        (ValueKind::Immediate(value), type_ir::BackendRepr::Scalar(..)) =>
                            arguments.push(value.try_into().unwrap()),
                        (ValueKind::Pair(value1, value2), type_ir::BackendRepr::ScalarPair(..)) => {    
                            arguments.push(value1.try_into().unwrap());
                            arguments.push(value2.try_into().unwrap());
                        }
                        (ValueKind::Ref(place), type_ir::BackendRepr::Memory) => {
                            // copy the place to a temporary location, so that mutations done in
                            // to it in the callee don't affect us, the caller
                            
                            let tmp = self.alloca_place(value.ty);
                            let place_value = self.load_value(place, value.ty);
                            place_value.store(tmp, value.ty, self);

                            arguments.push(tmp.value.into());
                        }
                        (kind, repr) => panic!("Value representaion should correspond to Layout represenation {kind:?}, {repr:?}"),
                    }
                }

                let result_ty = match ty {
                    Ty(TyKind::Function(def)) => {
                        let sig = self.generator.tcx.fn_sig(*def);
                        sig.returns
                    },
                    _ => panic!("{ty:?} is not callable")
                };
                let result_layout = self.generator.tcx.layout_of(result_ty).ok().unwrap();

                let mut ll_result = None;
                let mut mem_argload = None;
                match result_layout.repr {
                    type_ir::BackendRepr::Scalar(..) =>
                        ll_result = Some(()),
                    type_ir::BackendRepr::ScalarPair(_, scalar2) => {
                        ll_result = Some(());

                        let tmp = self.alloca_place(scalar2.get_type(self.generator.tcx));
                        arguments.push(tmp.value.into());

                        mem_argload = Some((tmp, scalar2.get_type(self.generator.tcx)));
                    }
                    type_ir::BackendRepr::Memory => {
                        // FIXME: For now this is fine, but since we might store into a place at
                        // the end anyway, there are cases where we could skip allocating the
                        // temporary and go straight to the provided place
                        // NOTE: this won't work for ScalarPairs as thier types won't match
                        if result_layout.size.in_bytes > 0 {
                            let tmp = self.alloca_place(result_ty);
                            arguments.push(tmp.value.into());

                            mem_argload = Some((tmp, result_ty));
                        }
                    }
                }

                let result = ensure!(self.builder.build_call(function.into_function_value(), &arguments, ""));
                let result = ll_result.map(|()| result);

                let value = match (result, mem_argload) {
                    (Some(result), None) => { // scalar return
                        Value {
                            kind: ValueKind::Immediate(result.as_any_value_enum()),
                            ty: result_ty
                        }
                    }
                    (Some(result), Some((sideload, ty))) => { // scalar pair return
                        let Value { kind: ValueKind::Immediate(llval), .. } = self.load_value(sideload, ty) else {
                            unreachable!()
                        };
                        Value {
                            kind: ValueKind::Pair(result.as_any_value_enum(), llval),
                            ty: result_ty
                        }
                    }
                    (None, Some((memload, ty))) => { // memory return
                        Value {
                            kind: ValueKind::Ref(memload),
                            ty
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

                let Value { kind: ValueKind::Immediate(lhs), ty: lhs_ty } = self.lower_operand(lhs) else {
                    panic!("RValue::BinaryOp is only valid for ValueKind::Immediate");
                };
                let Value { kind: ValueKind::Immediate(rhs), ty: rhs_ty } = self.lower_operand(rhs) else {
                    panic!("RValue::BinaryOp is only valid for ValueKind::Immediate");
                };
                match (lhs_ty, rhs_ty, op) {
                    (lhs_ty, rhs_ty, BinaryOp::Mul | BinaryOp::Add | BinaryOp::Sub) 
                        if let Ty(TyKind::Int(_, signed)) = lhs_ty && lhs_ty == rhs_ty => {
                        // this is a normal integer addition, mutliplication or subtraction
                        let lhs: ll::IntValue<'ll> = lhs.try_into().unwrap();
                        let rhs: ll::IntValue<'ll> = rhs.try_into().unwrap();

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
                            ty: lhs_ty
                        };
                        deferred.store_or_init(res, self);
                    }
                    (lhs_ty, _rhs_ty, BinaryOp::Div | BinaryOp::Rem) 
                        if let Ty(TyKind::Int(_, signed)) = lhs_ty => {
                        // this is a normal integer division and remainder
                        let lhs: ll::IntValue<'ll> = lhs.try_into().unwrap();
                        let rhs: ll::IntValue<'ll> = rhs.try_into().unwrap();

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
                            ty: lhs_ty
                        };
                        deferred.store_or_init(res, self);
                    }
                    (lhs_ty, _rhs_ty, BinaryOp::Shr) 
                        if let Ty(TyKind::Int(_, signed)) = lhs_ty => {
                        let lhs: ll::IntValue<'ll> = lhs.try_into().unwrap();
                        let rhs: ll::IntValue<'ll> = rhs.try_into().unwrap();

                        let res = ensure!(self.builder.build_right_shift(lhs, rhs, *signed, ""));
                        let res = Value {
                            kind: ValueKind::Immediate(res.into()),
                            ty: lhs_ty
                        };
                        deferred.store_or_init(res, self);
                    }
                    (lhs_ty, _rhs_ty, BinaryOp::Shl | BinaryOp::Xor | BinaryOp::Or | BinaryOp::And) 
                        if let Ty(TyKind::Int(..)) = lhs_ty => {
                        let lhs: ll::IntValue<'ll> = lhs.try_into().unwrap();
                        let rhs: ll::IntValue<'ll> = rhs.try_into().unwrap();

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
                            ty: lhs_ty
                        };
                        deferred.store_or_init(res, self);
                    }
                    (lhs_ty, _rhs_ty, BinaryOp::Eq | BinaryOp::Ne) 
                        if let Ty(TyKind::Int(..)) = lhs_ty => {
                        let lhs: ll::IntValue<'ll> = lhs.try_into().unwrap();
                        let rhs: ll::IntValue<'ll> = rhs.try_into().unwrap();

                        let predicate = match op {
                            BinaryOp::Eq => ll::IntPredicate::EQ,
                            BinaryOp::Ne => ll::IntPredicate::NE,
                            _ => unreachable!()
                        };

                        let res = ensure!(self.builder.build_int_compare(predicate, lhs, rhs, ""));
                        let res = Value {
                            kind: ValueKind::Immediate(res.into()),
                            ty: self.generator.tcx.basic_types.bool
                        };
                        deferred.store_or_init(res, self);
                    }
                    (lhs_ty, _rhs_ty, BinaryOp::Gt | BinaryOp::Ge | BinaryOp::Lt | BinaryOp::Le) 
                        if let Ty(TyKind::Int(.., signed)) = lhs_ty => {
                        let lhs: ll::IntValue<'ll> = lhs.try_into().unwrap();
                        let rhs: ll::IntValue<'ll> = rhs.try_into().unwrap();

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
                            ty: self.generator.tcx.basic_types.bool
                        };
                        deferred.store_or_init(res, self);
                    }
                    (lhs_ty, _rhs_ty, BinaryOp::Mul | BinaryOp::Div | BinaryOp::Rem | BinaryOp::Add | BinaryOp::Sub) 
                        if let Ty(TyKind::Float(_)) = lhs_ty => {
                        let lhs: ll::FloatValue<'ll> = lhs.try_into().unwrap();
                        let rhs: ll::FloatValue<'ll> = rhs.try_into().unwrap();

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
                            ty: lhs_ty
                        };
                        deferred.store_or_init(res, self);
                    }
                    (lhs_ty, _rhs_ty, BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Gt | BinaryOp::Ge | BinaryOp::Lt | BinaryOp::Le) 
                        if let Ty(TyKind::Float(_)) = lhs_ty => {
                        let lhs: ll::FloatValue<'ll> = lhs.try_into().unwrap();
                        let rhs: ll::FloatValue<'ll> = rhs.try_into().unwrap();

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
                            ty: self.generator.tcx.basic_types.bool
                        };
                        deferred.store_or_init(res, self);
                    }
                    (lhs_ty, rhs_ty, BinaryOp::Add | BinaryOp::Sub) 
                        if let Ty(TyKind::Refrence(ref_ty)) = lhs_ty && let Ty(TyKind::Int(..)) = rhs_ty => {
                        let lhs: ll::PointerValue<'ll> = lhs.try_into().unwrap();
                        let mut rhs: ll::IntValue<'ll> = rhs.try_into().unwrap();

                        if op == BinaryOp::Sub {
                            rhs = ensure!(self.builder.build_int_sub(rhs.get_type().const_int(0, false), rhs, ""));
                        }

                        let llvm_ty = match ref_ty {
                            Ty(TyKind::Void) => self.generator.context.i8_type().as_basic_type_enum(),
                            _ => ref_ty.llvm_type(self.generator).try_into().unwrap()
                        };

                        let res = ensure!(unsafe { self.builder.build_in_bounds_gep(llvm_ty, lhs, &[rhs], "") });
                        let res = Value {
                            kind: ValueKind::Immediate(res.into()),
                            ty: lhs_ty
                        };
                        deferred.store_or_init(res, self);
                    }
                    (lhs_ty, rhs_ty, BinaryOp::Sub) 
                        if let Ty(TyKind::Refrence(_)) = lhs_ty && lhs_ty == rhs_ty => {
                        let lhs: ll::PointerValue<'ll> = lhs.try_into().unwrap();
                        let rhs: ll::PointerValue<'ll> = rhs.try_into().unwrap();

                        let res = ensure!(self.builder.build_int_sub(lhs, rhs, ""));
                        let res = Value {
                            kind: ValueKind::Immediate(res.into()),
                            ty: self.generator.tcx.basic_types.nuint
                        };
                        deferred.store_or_init(res, self);
                    }
                    (lhs_ty, _rhs_ty, BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Gt | BinaryOp::Ge | BinaryOp::Lt | BinaryOp::Le) 
                        if let Ty(TyKind::Refrence(_)) = lhs_ty => {
                        let lhs: ll::PointerValue<'ll> = lhs.try_into().unwrap();
                        let rhs: ll::PointerValue<'ll> = rhs.try_into().unwrap();

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
                            ty: self.generator.tcx.basic_types.bool
                        };
                        deferred.store_or_init(res, self);
                    }
                    (lhs_ty, rhs_ty, op) =>
                        panic!("{op:?} is not defined between {lhs_ty:?} and {rhs_ty:?} and should not be caught here"),
                }

            }
            intermediate::RValue::Cast { value, ty: res_ty } => {
                let Value { kind: ValueKind::Immediate(llvm_value), ty: val_ty } = self.lower_operand(value) else {
                    panic!("RValue::BinaryOp is only valid for ValueKind::Immediate");
                };
                let res = match (val_ty, res_ty) {
                    (Ty(TyKind::Int(..)), Ty(TyKind::Int(_, signed))) => {
                        let int_value: ll::IntValue<'ll> = llvm_value.try_into().unwrap();
                        let int_type: ll::IntType<'ll> = res_ty.llvm_type(self.generator)
                            .try_into()
                            .unwrap();
                        ensure!(self.builder.build_int_cast_sign_flag(int_value, int_type, *signed, ""))
                            .as_any_value_enum()
                    }
                    (Ty(TyKind::Float(..)), Ty(TyKind::Float(..))) => {
                        let float_value: ll::FloatValue<'ll> = llvm_value.try_into().unwrap();
                        let float_type: ll::FloatType<'ll> = res_ty.llvm_type(self.generator)
                            .try_into()
                            .unwrap();
                        ensure!(self.builder.build_float_cast(float_value, float_type, ""))
                            .as_any_value_enum()
                    }
                    (Ty(TyKind::Int(_, signed)), Ty(TyKind::Float(..))) => {
                        let int_value: ll::IntValue<'ll> = llvm_value.try_into().unwrap();
                        let float_type: ll::FloatType<'ll> = res_ty.llvm_type(self.generator)
                            .try_into()
                            .unwrap();

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
                    ty: res_ty
                };
                deferred.store_or_init(res, self);
            }
            _ => todo!()
        }
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
                let layout = self.generator.tcx.layout_of(signature.returns)
                    .ok()
                    .unwrap();
                match layout.repr {
                    type_ir::BackendRepr::Scalar(_) => {
                        let value = self.lower_operand(value);
                        let Value { kind: ValueKind::Immediate(value), .. } = value else {
                            panic!("ValueKind should match BackendRepr");
                        };
                        let value: ll::BasicValueEnum<'ll> = value.try_into().unwrap();
                        ensure!(self.builder.build_return(Some(&value)));
                    }
                    type_ir::BackendRepr::ScalarPair(_scalar1, scalar2) => {

                        let value = self.lower_operand(value);
                        let Value { kind: ValueKind::Pair(value1, value2), .. } = value else {
                            panic!("ValueKind should match BackendRepr");
                        };

                        let argument: ll::PointerValue<'ll> = self.function.get_last_param()
                            .unwrap()
                            .try_into()
                            .unwrap();
                        let align = scalar2.align(self.generator).abi;
                        let place = Place { value: argument, align };
                        let scalar2_ty = scalar2.get_type(self.generator.tcx);
                        let value2 = Value {
                            kind: ValueKind::Immediate(value2),
                            ty: scalar2_ty
                        };
                        value2.store(place, scalar2_ty, self);

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
                                .try_into()
                                .unwrap();
                            let place = Place { value: argument, align: layout.align.abi };
                            let value = Value {
                                kind: ValueKind::Ref(value),
                                ty: signature.returns
                            };
                            value.store(place, signature.returns, self);
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
            let param_layout = self.generator.tcx.layout_of(param.ty)
                .ok()
                .unwrap();
            let reg = &body.local_registers[idx];
            debug_assert_eq!(reg.kind, intermediate::RegKind::Param);
            match param_layout.repr {
                type_ir::BackendRepr::Scalar(..) => {
                    let argument = self.function.get_nth_param(arg_idx)
                        .unwrap();
                    let kind = ValueKind::Immediate(argument.into());

                    let value = Value { kind, ty: param.ty };
                    if reg.mutability == Mutability::Const && !placebounds.contains(&idx) {
                        self.reg_translations[idx] = LocalKind::Value(value);
                    } else {
                        let place = self.alloca_place(param.ty);
                        value.store(place, param.ty, self);
                        self.reg_translations[idx] = LocalKind::Place { place, ty: param.ty };
                    }
                }
                type_ir::BackendRepr::ScalarPair(..) => {
                    let argument1 = self.function.get_nth_param(arg_idx)
                        .unwrap();
                    let argument2 = self.function.get_nth_param(arg_idx + 1)
                        .unwrap();
                    let kind = ValueKind::Pair(argument1.into(), argument2.into());

                    let value = Value { kind, ty: param.ty };
                    if reg.mutability == Mutability::Const && !placebounds.contains(&idx) {
                        self.reg_translations[idx] = LocalKind::Value(value);
                    } else {
                        let place = self.alloca_place(param.ty);
                        value.store(place, param.ty, self);
                        self.reg_translations[idx] = LocalKind::Place { place, ty: param.ty };
                    }

                    arg_idx += 2;
                    continue;
                }
                type_ir::BackendRepr::Memory => {
                    let argument: ll::PointerValue<'ll> = self.function.get_nth_param(arg_idx)
                        .unwrap()
                        .try_into()
                        .unwrap();
                    let align = self.generator.tcx.layout_of(param.ty).ok().unwrap().align.abi;
                    let place = Place { value: argument, align };
                    self.reg_translations[idx] = LocalKind::Place { place, ty: param.ty };
                }
            }
            arg_idx += 1;
        }

        for (id, register) in body.local_registers.iter_enumerated() {
            if register.kind == intermediate::RegKind::Local {
                let ty = register.ty;

                let place = self.alloca_place(ty);
                self.reg_translations[id] = LocalKind::Place { place, ty };
            } else if register.kind == intermediate::RegKind::Temp && placebounds.contains(&id) {
                let place = self.alloca_place(register.ty);
                self.reg_translations[id] = LocalKind::Place { place, ty: register.ty };
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

        let byte_type  = self.tcx.basic_types.byte.llvm_type(self).into_int_type();

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

        let clyde_name = item.ident().symbol;
        let function = module
            .add_function(
                &format!("clyde${}", clyde_name.get()),
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

impl<'tcx> TypeLayout<'tcx> {
    fn is_llvm_immediate(&self) -> bool {
        match self.repr {
            type_ir::BackendRepr::Scalar(..) => true,
            type_ir::BackendRepr::ScalarPair(..) | type_ir::BackendRepr::Memory => false,
        }
    }
}

fn llvm_lower_type_and_layout<'ll, 'tcx>(ty: Ty<'tcx>, layout: TypeLayout<'tcx>, ctxt: &CodegenCtxt<'ll, 'tcx>) -> ll::AnyTypeEnum<'ll> {
    if let type_ir::BackendRepr::Scalar(scalar) = layout.repr && !matches!(ty, Ty(TyKind::Bool)){
        return llvm_lower_scalar(scalar, ctxt);
    }

    match ty {
        Ty(TyKind::Bool) => 
            return ll::AnyTypeEnum::IntType(ctxt.context.bool_type()),
        // TODO: is never == void ok here?
        Ty(TyKind::Void | TyKind::Never) => 
            return ll::AnyTypeEnum::VoidType(ctxt.context.void_type()),
        Ty(TyKind::Function(def)) => {
            let signature = ctxt.tcx.fn_sig(*def);

            let result_ty = signature.returns;
            let result_layout = ctxt.tcx.layout_of(result_ty)
                .ok()
                .unwrap();

            let mut param_tys = Vec::<ll::BasicMetadataTypeEnum<'ll>>::with_capacity(signature.params.len());
            for param in signature.params {
                let layout = ctxt.tcx.layout_of(param.ty).ok().unwrap();
                match layout.repr {
                    type_ir::BackendRepr::Scalar(scalar) => { 
                        param_tys.push(llvm_lower_scalar(scalar, ctxt).try_into().unwrap());
                    }
                    type_ir::BackendRepr::ScalarPair(scalar1, scalar2) => {    
                        param_tys.push(llvm_lower_scalar(scalar1, ctxt).try_into().unwrap());
                        param_tys.push(llvm_lower_scalar(scalar2, ctxt).try_into().unwrap());
                    }
                    type_ir::BackendRepr::Memory => {
                        param_tys.push(ctxt.context.ptr_type(ll::AddressSpace::from(0)).into());
                    }
                }
            }
            return match result_layout.repr {
                type_ir::BackendRepr::Scalar(_) => {
                    let ret_ty: ll::BasicTypeEnum<'ll> = result_ty.llvm_type(ctxt).try_into().unwrap();
                    ll::AnyTypeEnum::FunctionType(ret_ty.fn_type(&param_tys, false))
                }
                type_ir::BackendRepr::ScalarPair(scalar1, _) => {
                    // scalar1 is the result_ty, scalar2 passed as an out pointer argument
                    param_tys.push(ctxt.context.ptr_type(ll::AddressSpace::from(0)).into());
                    let ret_ty: ll::BasicTypeEnum<'ll> = llvm_lower_scalar(scalar1, ctxt).try_into().unwrap();
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

