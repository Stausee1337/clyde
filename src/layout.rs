use index_vec::IndexVec;

use crate::{context::{FromCycleError, TyCtxt}, diagnostics::Message, syntax::{ast::{self, DefId}, lexer::Span}, target::{DataLayoutExt, TargetDataLayout}, type_ir::{AdtDef, AdtKind, Discriminant, Enum, FieldIdx, Float, GenericArgs, Instatiatable, Integer, Ty, TyKind}};

#[derive(Debug, Clone, Copy)]
#[repr(packed)]
pub struct ScalarValue {
    pub size: u8,
    pub data: u64
}

impl ScalarValue {
    pub fn from_char(c: char) -> Self {
        ScalarValue { data: c as u32 as u64, size: 4 }
    }

    pub fn from_boolean(b: bool) -> Self {
        ScalarValue { data: b as u8 as u64, size: 1 }
    }

    pub fn from_target_usize(provider: &impl DataLayoutExt, data: u64) -> Self {
        let ptr_size = provider.data_layout().ptr_size; 
        ScalarValue { size: u8::try_from(ptr_size.in_bytes).unwrap(), data: ptr_size.truncate(data) }
    }

    pub fn from_unsigned(data: u64, size: Size) -> Self {
        ScalarValue { size: u8::try_from(size.in_bytes).unwrap(), data }
    }

    pub fn try_to_target_usize<'tcx>(&self, tcx: TyCtxt<'tcx>) -> Option<u64> {
        self.to_unsigned(tcx.data_layout().ptr_size)
    }

    pub fn to_bits(&self, size: Size) -> Option<u64> {
        if size.in_bytes != self.size as u64 {
            return None
        }
        return Some(self.data)
    }

    pub fn to_unsigned(&self, size: Size) -> Option<u64> {
        self.to_bits(size)
    }
    
    pub fn to_signed(&self, size: Size) -> Option<i64> {
        let b = self.to_bits(size)?;
        Some(size.sign_extend(b))
    }
}

#[derive(Debug, Clone, Copy)]
pub enum ConstValue<'tcx> {
    Scalar(ScalarValue),
    ZeroSized,
    Memory {
        data: &'tcx [u8],
        align: Align
    },
}

#[derive(Debug, Clone, Copy, clyde_macros::Recursible)]
pub enum Const<'tcx> {
    Value {
        #[non_recursible]
        value: ConstValue<'tcx>,
        ty: Ty<'tcx>
    },
    Unevaluated {
        #[non_recursible]
        def: DefId,
        args: &'tcx GenericArgs<'tcx>,
        ty: Ty<'tcx>
    }
}

impl<'tcx> Const<'tcx> {
    pub fn from_boolean(tcx: TyCtxt<'tcx>, b: bool) -> Self {
        let value = ConstValue::Scalar(ScalarValue::from_boolean(b));
        Const::Value { value, ty: tcx.basic_types.bool }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Endianness {
    Little, Big
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Align {
    pow2: u8
}

impl Align {
    pub const ONE: Align = Align::from_bytes(1);
    pub const LLVM_MAX_ALIGN: u32 = 29;

    pub const fn from_bits(bits: u64) -> Self {
        Self::from_bytes((bits + 7) / 8)
    }

    pub const fn from_bytes(size: u64) -> Self {
        // TODO: make this function fallible when users can request specific type alignment
        let zeros = size.trailing_zeros();
        if size != (1 << zeros) {
            panic!("non power of 2 alignment");
        }
        if zeros > Self::LLVM_MAX_ALIGN {
            panic!("to big alignment: > 536870912");
        }
        Self { pow2: zeros as u8 }
    }

    pub const fn in_bytes(&self) -> u64 {
        1 << (self.pow2 as u64)
    }
}

impl std::fmt::Debug for Align {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Align({})", 1 << self.pow2)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Size {
    pub in_bytes: u64
}

impl Size {
    pub const fn from_bits(bits: u64) -> Self {
        Size { in_bytes: (bits + 7) / 8 }
    }

    pub fn from_bytes(bytes: impl TryInto<u64>) -> Self {
        Size { in_bytes: bytes.try_into().map_err(|_| "u64 conversion failure in Size::from_bytes").unwrap() }
    }

    pub const fn align_up(&self, align: Align) -> u64 {
        let align_mask = align.in_bytes() - 1;
        if self.in_bytes & align_mask == 0 {
            self.in_bytes // already aligned
        } else {
            // FIXME: Replace with .expect, once `Option::expect` is const.
            if let Some(aligned) = (self.in_bytes | align_mask).checked_add(1) {
                aligned
            } else {
                panic!("attempt to add with overflow")
            }
        }
    }

    pub fn in_bits(&self) -> u64 {
        self.in_bytes * 8
    }

    pub fn truncate(&self, x: u64) -> u64 {
        if self.in_bytes == 0 {
            return 0;
        }
        let bits = 64 - self.in_bits();
        (x << bits) >> bits
    }

    pub fn sign_extend(&self, x: u64) -> i64 {
        if self.in_bytes == 0 {
            return 0;
        }
        let bits = 64 - self.in_bits();
        ((x << bits) as i64) >> bits
    }
}

impl Integer {
    pub fn size(&self, provider: &impl DataLayoutExt) -> Size {
        let data_layout = provider.data_layout();
        use Integer::*;
        match self {
            I8 => Size::from_bits(8),
            I16 => Size::from_bits(16),
            I32 => Size::from_bits(32),
            I64 => Size::from_bits(64),
            ISize => data_layout.ptr_size
        }
    }

    pub fn align(&self, provider: &impl DataLayoutExt) -> Align {
        let data_layout = provider.data_layout();
        use Integer::*;
        match self {
            I8 => data_layout.i8_align,
            I16 => data_layout.i16_align,
            I32 => data_layout.i32_align,
            I64 => data_layout.i64_align,
            ISize => data_layout.ptr_align
        }
    }

    pub fn normalize(&self, provider: &impl DataLayoutExt) -> Self {
        let Integer::ISize = self else {
            return *self;
        };
        let data_layout = provider.data_layout();
        match data_layout.ptr_size.in_bytes {
            1 => Integer::I8,
            2 => Integer::I16,
            4 => Integer::I32,
            8 => Integer::I64,
            _ => unreachable!("target has invalid ISize")
        }
    }
}

impl Float {
    pub fn size(&self) -> Size {
        match self {
            Float::F32 => Size::from_bits(32),
            Float::F64 => Size::from_bits(64),
        }
    }

    pub fn align(&self, provider: &impl DataLayoutExt) -> Align {
        let data_layout = provider.data_layout();
        match self {
            Float::F32 => data_layout.f32_align,
            Float::F64 => data_layout.f64_align,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Fields {
    /// For Scalar types being backed exclusively BackendRepr::Scalar
    Scalar,
    /// For fix-size Array types
    Array {
        stride: u64,
        count: u64
    },
    /// Including but not limited to structure types, zst types, functions, etc
    Struct {
        fields: IndexVec<FieldIdx, u64>
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Scalar {
    Int(Integer, bool),
    Float(Float),
    Pointer
}

impl Scalar {
    pub fn align(&self, provider: &impl DataLayoutExt) -> Align {
        match self {
            Scalar::Int(int, _) => int.align(provider),
            Scalar::Float(float) => float.align(provider),
            Scalar::Pointer => {
                let data_layout = provider.data_layout();
                data_layout.ptr_align
            }
        }
    }

    pub fn size(&self, provider: &impl DataLayoutExt) -> Size {
        match self {
            Scalar::Int(int, _) => int.size(provider),
            Scalar::Float(float) => float.size(),
            Scalar::Pointer => {
                let data_layout = provider.data_layout();
                data_layout.ptr_size
            }
        }
    }

    pub fn get_type<'tcx>(&self, tcx: TyCtxt<'tcx>) -> Ty<'tcx> {
        match *self {
            Scalar::Int(int, signed) =>
                Ty::new_int(tcx, int, signed),
            Scalar::Float(float) =>
                Ty::new_float(tcx, float),
            Scalar::Pointer =>
                Ty::new_refrence(tcx, tcx.basic_types.void)
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BackendRepr {
    Scalar(Scalar),
    ScalarPair(Scalar, Scalar),
    Memory
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct LayoutData {
    pub size: Size,
    pub align: Align,
    pub fields: Fields,
    pub repr: BackendRepr
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TyLayoutTuple<'tcx> {
    pub ty: Ty<'tcx>,
    pub layout: Layout<'tcx>
}

impl<'tcx> std::ops::Deref for TyLayoutTuple<'tcx> {
    type Target = LayoutData;

    fn deref(&self) -> &Self::Target {
        self.layout.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Layout<'tcx>(pub &'tcx LayoutData);

impl<'tcx> std::ops::Deref for Layout<'tcx> {
    type Target = LayoutData;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

impl<'tcx> Layout<'tcx> {
    fn new(tcx: TyCtxt<'tcx>, size: Size, align: Align, fields: Fields, repr: BackendRepr) -> Self {
        tcx.intern_layout(LayoutData { size, align, fields, repr })
    }
}

#[derive(Debug, Clone, Copy)]
pub enum LayoutError {
    /// The Ty was erroneous to begin with (TyKind::Error), no sensible layout can be computed
    Erroneous,
    /// A struct is too big for the backend to handle, or an enum has to many variants for the
    /// representation chosen
    TooBig,
    /// For the type provided no sensible layout can be computed as it is not specific. This can
    /// happen for `Param` or `Infer` types.
    Inspecific,
    /// The Ty's layout is cyclic: Ty contains itself without any indirection
    Cyclic
}

impl<'tcx> FromCycleError<'tcx> for Result<TyLayoutTuple<'tcx>, LayoutError> {
    fn from_cycle_error(_tcx: TyCtxt<'tcx>) -> Self {
        Result::Err(LayoutError::Cyclic)
    }
}

struct LayoutCtxt<'tcx> {
    tcx: TyCtxt<'tcx>,
    data_layout: TargetDataLayout
}

impl<'tcx> LayoutCtxt<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            data_layout: *tcx.data_layout()
        }
    }

    fn layout_for_array_like(&self, dynamic_sized: bool) -> Layout<'tcx> {
        let data_layout = self.data_layout();
        let align = data_layout.ptr_align;
        let ptr_size = data_layout.ptr_size;

        let nuint = Scalar::Int(Integer::ISize.normalize(self), false);

        let mut fields = IndexVec::new();
        fields.push(0);
        fields.push(ptr_size.in_bytes);
        if dynamic_sized {
            fields.push(ptr_size.in_bytes * 2);
        }

        Layout::new(
            self.tcx,
            Size::from_bytes(ptr_size.in_bytes * (2 + dynamic_sized as u64)),
            align,
            Fields::Struct { fields },
            if !dynamic_sized {
                BackendRepr::ScalarPair(Scalar::Pointer, nuint)
            } else {
                BackendRepr::Memory
            }
        )
    }

    fn layout_for_integer(&self, integer: Integer, signedness: bool) -> Layout<'tcx> {
        let size = integer.size(self);
        let align = integer.align(self);
        Layout::new(
            self.tcx,
            size,
            align,
            Fields::Scalar,
            BackendRepr::Scalar(Scalar::Int(integer, signedness))
        )
    }

    fn layout_for_float(&self, float: Float) -> Layout<'tcx> {
        let size = float.size();
        let align = float.align(self);
        Layout::new(
            self.tcx,
            size,
            align,
            Fields::Scalar,
            BackendRepr::Scalar(Scalar::Float(float))
        )
    }

    fn layout_for_struct(&self, fields: IndexVec<FieldIdx, Layout<'tcx>>) -> Layout<'tcx> {
        let mut align = Align::ONE;
        let mut offset = 0;
        let mut offsets = IndexVec::new();
        let mut size = 0;
        for field in &fields {
            size += field.size.in_bytes;
            align = std::cmp::max(align, field.align);
            if offset % field.align.in_bytes() != 0 {
                offset = align_up(offset, field.align);
            }
            offsets.push(offset);
        }

        let mut repr = BackendRepr::Memory;

        let mut fiter = fields.iter();
        match (fiter.next(), fiter.next(), fiter.next()) {
            (Some(field), None, None) => {
                match field.repr {
                    frepr @ BackendRepr::Scalar(..) => repr = frepr,
                    frepr @ BackendRepr::ScalarPair(..) => repr = frepr,
                    _ => ()
                }
            }
            (Some(field1), Some(field2), None) if let BackendRepr::Scalar(scalar1) = field1.repr && let BackendRepr::Scalar(scalar2) = field2.repr =>
                repr = BackendRepr::ScalarPair(scalar1, scalar2),
            _ => ()
        }


        Layout::new(
            self.tcx,
            Size::from_bytes(size),
            align,
            Fields::Struct { fields: offsets },
            repr
        )
    }

    fn layout_for_array(&self, ty: Ty<'tcx>, count: u64) -> Result<Layout<'tcx>, LayoutError> {
        let tuple = match self.tcx.layout_of(ty) {
            Ok(tuple) => tuple,
            Err(LayoutError::Cyclic) => {
                // A type refrencing itself like this should only be possible using type aliases 
                // (NOTE: in the future maybe through compile-time meta programming)
                // TODO: once type aliases become a thing: unintern the Ty IR into it's AST Node
                todo!("type alias cyclic types");
            }
            Err(err) => return Err(err)
        };
        let align = tuple.layout.align;
        Ok(Layout::new(
            self.tcx,
            Size { in_bytes: count * tuple.layout.size.in_bytes },
            align,
            Fields::Array { stride: tuple.layout.size.in_bytes, count },
            BackendRepr::Memory
        ))
    }

    fn layout_for_enum(&self, enm: &'tcx Enum<'tcx>) -> Result<Layout<'tcx>, LayoutError> {
        if let Some(Ty(TyKind::Err)) = enm.representation {
            return Err(LayoutError::Erroneous);
        }
        let mut prev_discriminant: i128 = 0;
        let mut min_discriminant = i128::MAX;
        let mut max_discriminant = i128::MIN;
        let mut erroneous = false;
        for variant in &enm.variants {
            let discriminant = match variant.discriminant {
                Discriminant::Explicit { def } => {
                    let ty = self.tcx.type_of(def);
                    let cnst = self.tcx.constant_of(def);
                    // TODO: `.instantiate();` with ambient generic args
                    let cnst = match self.tcx.evaluate_ty_const(cnst) {
                        Ok(r) => r,
                        Err(..) => {
                            erroneous = true;
                            continue;
                        }
                    };

                    let ConstValue::Scalar(scalar) = cnst else {
                        unreachable!("non ::Scalar enum values aren't allowed")
                    };

                    let Ty(&TyKind::Int(int, signed)) = ty else {
                        unreachable!()
                    };

                    let size = int.size(&self.tcx);
                    prev_discriminant = if !signed {
                        scalar.to_unsigned(size).unwrap() as i128
                    } else {
                        scalar.to_signed(size).unwrap() as i128
                    };
                    prev_discriminant
                }
                Discriminant::Relative { offset } => {
                    prev_discriminant + offset as i128
                }
            };
            min_discriminant = min_discriminant.min(discriminant);
            max_discriminant = max_discriminant.max(discriminant);
        }
        if erroneous {
            return Err(LayoutError::Erroneous);
        }

        let repr = match enm.representation {
            Some(repr) => {
                let layout = self.tcx.layout_of(repr)?;
                let BackendRepr::Scalar(Scalar::Int(int, signed)) = layout.repr else {
                    unreachable!()
                };

                if min_discriminant < 0 && !signed {
                    let ast::Node::Item(item) = self.tcx.node_by_def_id(enm.def) else { unreachable!() };
                    Message::error(format!("some variants of enum `{}` have negative discriminats", enm.name))
                        .at(item.span)
                        .note(format!("specifiy a signed represenation, using `enum {}: <type>`", enm.name))
                        .push(self.tcx.diagnostics());
                    return Err(LayoutError::TooBig);
                }
                
                let fit_fn = |value: i128| {
                    if signed {
                        Integer::fit_signed(value).unwrap()
                    } else {
                        Integer::fit_unsigned(value as u64)
                    }
                };

                let min_size = fit_fn(min_discriminant).size(self).max(fit_fn(max_discriminant).size(self));
                if int.size(self) < min_size {
                    let ast::Node::Item(item) = self.tcx.node_by_def_id(enm.def) else { unreachable!() };
                    Message::error(format!("all variants in enum `{}` don't fit into representation of {repr}", enm.name))
                        .at(item.span)
                        .note(format!("specifiy a bigger represenation, using `enum {}: <type>`", enm.name))
                        .push(self.tcx.diagnostics());
                    return Err(LayoutError::TooBig);
                }

                repr
            }
            None if enm.variants.len() > 0 => {
                let a = Integer::fit_signed(min_discriminant).unwrap();
                let Some(b) = Integer::fit_signed(max_discriminant) else {
                    let ast::Node::Item(item) = self.tcx.node_by_def_id(enm.def) else { unreachable!() };
                    Message::error(format!("variants of enum `{}` don't fit into a sigend integer", enm.name))
                        .at(item.span)
                        .note(format!("specifiy a specific represenation, using `enum {}: <type>`", enm.name))
                        .push(self.tcx.diagnostics());
                    return Err(LayoutError::TooBig);
                };
                let size = a.size(self).max(b.size(self));

                if size <= Integer::I32.size(self) {
                    self.tcx.basic_types.int
                } else {
                    Ty::new_int(self.tcx, Integer::I64, true)
                }
            }
            None => self.tcx.basic_types.int
        };

        Ok(self.tcx.layout_of(repr)?.layout)
    }

    fn calculate_layout_for_ty(&self, ty: Ty<'tcx>) -> Result<TyLayoutTuple<'tcx>, LayoutError> {
        let layout = match ty {
            Ty(TyKind::Void) | Ty(TyKind::Never) =>
                Layout::new(
                    self.tcx,
                    Size::from_bytes(0),
                    Align::ONE,
                    Fields::Struct { fields: IndexVec::new() },
                    BackendRepr::Memory
                ),
            Ty(TyKind::Bool) =>
                self.tcx.layout_of(self.tcx.basic_types.byte)?.layout,
            Ty(TyKind::Char) =>
                self.tcx.layout_of(self.tcx.basic_types.uint)?.layout,
            Ty(TyKind::String) =>
                self.layout_for_array_like(false),
            Ty(TyKind::Int(integer, signedness)) =>
                self.layout_for_integer(*integer, *signedness),
            Ty(TyKind::Float(float)) =>
                self.layout_for_float(*float),
            Ty(TyKind::Enum(enm)) => 
                self.layout_for_enum(enm)?,
            Ty(TyKind::Adt(adt, generics)) => {
                match adt {
                    AdtDef(AdtKind::Struct(strct)) => {
                        let mut fields = IndexVec::new();
                        for field in strct.fields.iter() {
                            let tuple = match self.tcx.layout_of(self.tcx.type_of(field.def).instantiate(*generics, self.tcx)) {
                                Ok(tuple) => tuple,
                                err @ Err(LayoutError::Cyclic) => {
                                    let ast::Node::Item(item) = self.tcx.node_by_def_id(strct.def) else { unreachable!() };
                                    let ast::Node::FieldDef(def) = self.tcx.node_by_def_id(field.def) else { unreachable!() };
                                    self.report_cycle_error(item.ident().span, def.ty.span, format_args!("struct `{}`", strct.name.get()));
                                    return err;
                                }
                                err @ Err(_) => return err
                            };
                            fields.push(tuple.layout); 
                        }
                        self.layout_for_struct(fields)
                    }
                    AdtDef(AdtKind::Union) => todo!(),
                }
            }
            Ty(TyKind::Refrence(..)) => {
                let data_layout = self.data_layout();
                Layout::new(
                    self.tcx,
                    data_layout.ptr_size,
                    data_layout.ptr_align,
                    Fields::Scalar,
                    BackendRepr::Scalar(Scalar::Pointer)
                )
            }
            Ty(TyKind::Range(..)) => todo!(),
            Ty(TyKind::Slice(_)) =>
                self.layout_for_array_like(false),
            Ty(TyKind::Array(base, count)) => {
                let count = count.try_to_target_usize(self.tcx)
                    .unwrap();
                self.layout_for_array(*base, count)?
            }
            Ty(TyKind::Tuple(tys)) => {
                let mut fields = IndexVec::new();
                for ty in tys.iter() {
                    let tuple = match self.tcx.layout_of(*ty) {
                        Ok(tuple) => tuple,
                        Err(LayoutError::Cyclic) => {
                            // A type refrencing itself like this should only be possible using type aliases 
                            // (NOTE: in the future maybe through compile-time meta programming)
                            // TODO: once type aliases become a thing: unintern the Ty IR into it's AST Node
                            todo!("type alias cyclic types");
                        }
                        err @ Err(_) => return err
                    };
                    fields.push(tuple.layout); 
                }
                self.layout_for_struct(fields)
            },
            Ty(TyKind::DynamicArray(_)) =>
                self.layout_for_array_like(true),
            Ty(TyKind::Function(..)) => 
                Layout::new(
                    self.tcx,
                    Size::from_bytes(0),
                    Align::ONE,
                    Fields::Struct { fields: IndexVec::new() },
                    BackendRepr::Memory
                ),
            Ty(TyKind::Param(_)) => return Err(LayoutError::Inspecific),
            Ty(TyKind::Err) => return Err(LayoutError::Erroneous),
        };
        Ok(TyLayoutTuple { ty, layout })
    }

    fn report_cycle_error(&self, item_span: Span, recursion_span: Span, kind: std::fmt::Arguments) {
        Message::error(format!("infinite size {} contains itself without indirection", kind))
            .at(item_span)
            .hint(format!("recursion without indirection"), recursion_span)
            .push(self.tcx.diagnostics());
    }
}

impl<'tcx> DataLayoutExt for LayoutCtxt<'tcx> {
    fn data_layout(&self) -> &TargetDataLayout {
        &self.data_layout
    }
}

pub fn layout_of<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Result<TyLayoutTuple<'tcx>, LayoutError> {
    let ctxt = LayoutCtxt::new(tcx);
    ctxt.calculate_layout_for_ty(ty)
}

#[inline]
const fn align_up(addr: u64, align: Align) -> u64 {
    let align_mask = align.in_bytes() - 1;
    if addr & align_mask == 0 {
        addr // already aligned
    } else {
        // FIXME: Replace with .expect, once `Option::expect` is const.
        if let Some(aligned) = (addr | align_mask).checked_add(1) {
            aligned
        } else {
            panic!("attempt to add with overflow")
        }
    }
}
