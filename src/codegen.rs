use std::{cell::RefCell, collections::VecDeque};

use index_vec::IndexVec;
use ll::{BasicType, AnyValue};
use hashbrown::{HashMap, hash_map::Entry};

use crate::{analysis::intermediate, context::TyCtxt, syntax::ast, target::{DataLayoutExt, TargetDataLayout}, type_ir::{self, AdtDef, AdtKind, Const, ConstKind, Ty, TyKind, TypeLayout}};
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

#[derive(Clone, Copy)]
struct Place<'ll> {
     value: ll::PointerValue<'ll>,
     align: type_ir::Align,
}

#[derive(Clone, Copy)]
enum ValueKind<'ll> {
     Ref(Place<'ll>),
     Immediate(ll::AnyValueEnum<'ll>),
     Pair(ll::AnyValueEnum<'ll>, ll::AnyValueEnum<'ll>),
}

#[derive(Clone, Copy)]
struct Value<'ll, 'tcx> {
    kind: ValueKind<'ll>,
    ty: Ty<'tcx>
}

impl<'ll, 'tcx> Value<'ll, 'tcx> {
    fn deref<'a>(&self, builder: &mut CodeBuilder<'a, 'll, 'tcx>) -> Place<'ll> {
        match self.kind {
            ValueKind::Immediate(value) => {
                let layout = builder.generator.tcx.layout_of(self.ty)
                    .ok()
                    .unwrap();
                Place {
                    value: value.into_pointer_value(),
                    align: layout.align.abi
                }
            }
            ValueKind::Pair(..) =>
                panic!("ValueKimd::Pair doesn't specify a place"),
            ValueKind::Ref(..) =>
                panic!("cannot deref ValueKind::Ref - just use its place directly")
        }
    }

    fn store<'a>(&self, 
        dest: Place<'ll>,
        ty: Ty<'tcx>,
        builder: &mut CodeBuilder<'a, 'll, 'tcx>
    ) {

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
        todo!()
    }

    fn alloca_place(&mut self, llvm_ty: impl BasicType<'ll>, align: type_ir::Align) -> Place<'ll> {
        let pointer = ensure!(self.builder.build_alloca(llvm_ty, ""));
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
                (value.deref(self), value.ty)
            }
            LocalKind::Dangling => panic!("tried to resolve a LocalKind::Dangling")
        };
        match ir_place {
            Deref(_) => (cg_place, ty),
            Register(_) => (cg_place, ty),
            Field { field, ty: res_ty, .. } => {
                let llvm_ty: ll::BasicTypeEnum<'ll> = ty.llvm_type(self.generator)
                    .try_into()
                    .unwrap();

                let layout = self.generator.tcx.layout_of(ty)
                    .ok()
                    .unwrap();
                let value = ensure!(self.builder.build_struct_gep(llvm_ty, cg_place.value, field.raw(), ""));
                (Place { value, align: layout.align.abi }, res_ty)
            }
            Index { idx: _idx, .. } => {
                // TODO: Index is more complicated as it needs to work on (arrays, slices, dynamic
                // arrays, ptr) and we first need to understand the ty we are operating on. Also
                // the idx Operand can be Constant or Copy leading to two different codepaths. The
                // constant case should propably generate `extractvalue` while the runtime case
                // should generate `inbounds_gep`
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
                    let byte_type  = self.generator.tcx.basic_types.byte.llvm_type(self.generator).into_int_type();  

                    let mut values = Vec::with_capacity(string_data.len());
                    for byte in string_data {
                        values.push(byte_type.const_int(*byte as u64, false));
                    }
                    let data = byte_type.const_array(&values);
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
                let (cg_place, ty) = self.lower_place(ir_place);
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
                let mut arguments = vec![];
                for arg in args {
                    let value = self.lower_operand(arg.operand);

                    let layout = self.generator.tcx.layout_of(value.ty).ok().unwrap();
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
                            
                            let llvm_ty: ll::BasicTypeEnum<'ll> = value.ty.llvm_type(self.generator).try_into().unwrap();
                            let tmp = self.alloca_place(llvm_ty, layout.align.abi);
                            let place_value = self.load_value(place, value.ty);
                            place_value.store(tmp, value.ty, self);

                            arguments.push(tmp.value.into());
                        }
                        _ => panic!("Value representaion should correspond to Layout represenation"),
                    }
                }

                let Value { kind: ValueKind::Immediate(function), ty } = self.lower_operand(callee) else {
                    panic!("function value needs to be ValueKind::Immediate");
                };

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

                        let llvm_ty: ll::BasicTypeEnum<'ll> = llvm_lower_scalar(scalar2, self.generator).try_into().unwrap();
                        let tmp = self.alloca_place(llvm_ty, scalar2.align(self.generator).abi);
                        arguments.push(tmp.value.into());

                        mem_argload = Some((tmp, scalar2.get_type(self.generator.tcx)));
                    }
                    type_ir::BackendRepr::Memory => {
                        // FIXME: For now this is fine, but since we might store into a place at
                        // the end anyway, there are cases where we could skip allocating the
                        // temporary and go straight to the provided place
                        // NOTE: this won't work for ScalarPairs as thier types won't match
                        let llvm_ty: ll::BasicTypeEnum<'ll> = result_ty.llvm_type(self.generator).try_into().unwrap();
                        let tmp = self.alloca_place(llvm_ty, result_layout.align.abi);
                        arguments.push(tmp.value.into());

                        mem_argload = Some((tmp, result_ty));
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
                    (None, None) => unreachable!()
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
                            ty: lhs_ty
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
                            ty: lhs_ty
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
                            ty: lhs_ty
                        };
                        deferred.store_or_init(res, self);
                    }
                    (lhs_ty, rhs_ty, op) =>
                        panic!("{op:?} is not defined between {lhs_ty:?} and {rhs_ty:?} and should not be caught here"),
                }

            }
            _ => todo!()
        }
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
        self.reg_translations.resize_with(
            body.local_registers.len(), Default::default);

        for (idx, register) in body.local_registers.iter_enumerated().take(body.num_params) {
            debug_assert_eq!(register.kind, intermediate::RegKind::Param);
            let ty = register.ty;
            let kind = ValueKind::Immediate(self.function.get_nth_param(idx.raw()).unwrap().into());
            // FIXME: alloca and copy to stack and use LocalKind::Place for every mutable param
            // (trying to mutate params at the moment will crash)
            self.reg_translations[idx] = LocalKind::Value(Value { kind, ty });
        }

        let entry = self.resolve_block(body.entry);
        self.builder.position_at_end(entry);
        for (id, register) in body.local_registers.iter_enumerated() {
            if register.kind != intermediate::RegKind::Local {
                continue;
            }

            let ty = register.ty;

            let llvm_ty: ll::BasicTypeEnum<'ll> = ty.llvm_type(self.generator)
                .try_into().unwrap();
            let align = self.generator.tcx.layout_of(ty).ok().unwrap().align.abi;

            let place = self.alloca_place(llvm_ty, align);
            self.reg_translations[id] = LocalKind::Place { place, ty };
        }

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
                        // in param deduction between here and function calling
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
        types::{AnyTypeEnum, BasicTypeEnum, BasicMetadataTypeEnum, BasicType},
        values::{IntValue, FloatValue, FunctionValue, AnyValueEnum, PointerValue, AnyValue},
        AddressSpace,
        IntPredicate,
        FloatPredicate
    };
}

