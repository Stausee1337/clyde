use core::panic;
use std::{hash::Hash, marker::PhantomData, ops::Deref, ptr::NonNull};

use index_vec::IndexVec;

use crate::{context::{self, FromCycleError, Internable, InternerExt, Interners, Lift, TyCtxt}, inline_slice::InlineSlice, layout::Size, mapping::{self, Mapper, Recursible}, pretty_print::{PrettyPrinter, Print}, syntax::{ast::{self, DefId, NodeId}, symbol::{sym, Symbol}}, target::DataLayoutExt};

impl DefId {
    pub fn normalized_generics<'tcx>(&self, tcx: TyCtxt<'tcx>) -> &'tcx GenericArgs<'tcx> {
        let node = tcx.node_by_def_id(*self);
        let generics = node.generics();

        let mut generic_args = vec![];
        for param in generics {
            let def_id = *param.def_id.get().unwrap();
            let generic_arg = match param.kind {
                ast::GenericParamKind::Type(..) =>
                    GenericArg::from_ty(tcx.type_of(def_id)),
                ast::GenericParamKind::Const(..) => 
                    GenericArg::from_const(tcx.constant_of(def_id)),
            };
            generic_args.push(generic_arg);
        }
        
        tcx.make_args(&generic_args)
    }
}

pub trait Instatiatable<'tcx> {
    fn instantiate(self, generic_args: &'tcx GenericArgs<'tcx>, tcx: TyCtxt<'tcx>) -> Self;
}

impl<'tcx, T: mapping::Recursible<'tcx>> Instatiatable<'tcx> for T {
    fn instantiate(self, generic_args: &'tcx GenericArgs<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        let mut handler = mapping::InstantiationMapper::new(tcx, generic_args);
        self.map_recurse(&mut handler)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GenericArg<'tcx> {
    ptr: NonNull<()>,
    phantom: PhantomData<&'tcx ()>
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GenericArgKind<'tcx> {
    Ty(Ty<'tcx>),
    Const(Const<'tcx>),
}

impl<'tcx> GenericArg<'tcx> {
    const TY_ENCODED: usize = 0b01;
    const CONST_ENCODED: usize = 0b10;
    const ENCODING_MASK: usize = 0b11;

    pub fn from_ty(ty: Ty<'tcx>) -> Self {
        let ptr = unsafe { Self::pack(ty.0, Self::TY_ENCODED) };
        Self {
            ptr,
            phantom: PhantomData
        }
    }

    pub fn from_const(cnst: Const<'tcx>) -> Self {
        let ptr = unsafe { Self::pack(cnst.0, Self::CONST_ENCODED) };
        Self {
            ptr,
            phantom: PhantomData
        }
    }

    pub fn kind(self) -> GenericArgKind<'tcx> {
        let kind = self.ptr.addr().get() & Self::ENCODING_MASK;
        match kind {
            Self::TY_ENCODED => GenericArgKind::Ty(Ty(unsafe { self.unpack() })),
            Self::CONST_ENCODED => GenericArgKind::Const(Const(unsafe { self.unpack() })),
            _ => panic!("invalid generic argument encoding"),
        }
    }

    #[inline]
    unsafe fn unpack<T>(self) -> &'tcx T {
        let addr = self.ptr.addr().get() & !Self::ENCODING_MASK;
        std::mem::transmute(addr as *const T)
    }

    #[inline]
    unsafe fn pack<T>(refrence: &T, encoded: usize) -> NonNull<()> {
        assert!(std::mem::align_of::<T>() >= 4);
        let addr = (refrence as *const T).addr();
        NonNull::new_unchecked((addr | encoded) as *mut ())
    }
}

impl<'tcx> std::fmt::Display for GenericArg<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.kind() {
            GenericArgKind::Ty(ty) => write!(f, "{ty}"),
            GenericArgKind::Const(cnst) => write!(f, "{cnst}"),
        }
    }
}

impl<'tcx> mapping::Recursible<'tcx> for GenericArg<'tcx> {
    fn map_recurse(self, handler: &mut impl mapping::Mapper<'tcx>) -> Self {
        match self.kind() {
            GenericArgKind::Ty(ty) =>
                GenericArg::from_ty(mapping::Recursible::map_recurse(ty, handler)),
            GenericArgKind::Const(cnst) =>
                GenericArg::from_const(mapping::Recursible::map_recurse(cnst, handler)),
        }
    }
}

pub type GenericArgs<'tcx> = InlineSlice<GenericArg<'tcx>>;

impl<'tcx> Recursible<'tcx> for &'tcx GenericArgs<'tcx> {
    fn map_recurse(self, handler: &mut impl Mapper<'tcx>) -> Self {
        let result = self
            .iter()
            .map(|x| Recursible::map_recurse(*x, handler))
            .collect::<Vec<_>>();
        handler.tcx().make_args(&result)
    }
}

impl<'a> Lift for &'a GenericArgs<'a> {
    type Lifted<'tcx> = &'tcx GenericArgs<'tcx>;

    fn lift<'tcx>(self, tcx: TyCtxt<'tcx>) -> Option<&'tcx GenericArgs<'tcx>> {
        if self == GenericArgs::empty() {
            return Some(GenericArgs::empty());
        }
        tcx.interners.args
            .contains(self.as_slice())
            .then(|| unsafe { std::mem::transmute(self) })

    }
}

impl<'tcx> Internable for &'tcx GenericArgs<'tcx> {
    fn to_pointer(self) -> *const () {
        self as *const _ as *const ()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Instance<'tcx> {
    pub def: DefId,
    pub args: &'tcx GenericArgs<'tcx>
}

impl<'tcx> std::fmt::Display for Instance<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        context::with_tcx(|tcx| {
            let tcx = *tcx.unwrap();

            PrettyPrinter::print_to_formatter(tcx, f, |p| {
                let args = tcx.lift(self.args).unwrap();
                Instance { def: self.def, args }.print(p)
            })
        })
    }
}

#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq)]
pub struct AdtDef<'tcx>(pub &'tcx AdtKind);

impl<'tcx> Deref for AdtDef<'tcx> {
    type Target = AdtKind;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

#[derive(Debug, Hash)]
#[repr(u32)]
pub enum AdtKind {
    Struct(Struct),
    Union,
}

impl AdtKind {
    pub fn def(&self) -> DefId {
        match self {
            AdtKind::Struct(strct) => strct.def,
            AdtKind::Union => todo!()
        }
    }

    pub fn name(&self) -> Symbol {
        match self {
            AdtKind::Struct(strct) => strct.name,
            AdtKind::Union => todo!()
        }
    }

    pub fn kind(&self) -> &'static str {
        match self {
            AdtKind::Struct(..) => "struct",
            AdtKind::Union => "union"
        }
    }
}

impl PartialEq for AdtKind {
    fn eq(&self, other: &Self) -> bool {
        self.def() == other.def()
    }
}

impl Eq for AdtKind {}

#[derive(Debug, Hash)]
pub struct Struct {
    pub def: DefId,
    pub name: Symbol,
    pub fields: IndexVec<FieldIdx, FieldDef>,
}

impl Struct {
    pub fn new(
        def: DefId,
        name: Symbol,
        fields: IndexVec<FieldIdx, FieldDef>,
    ) -> Self {
        Self { def, name, fields }
    }

    pub fn fields(&self) -> impl Iterator<Item = (FieldIdx, &FieldDef)> {
        self.fields.iter_enumerated()
    }

    pub fn get_field(&self, field: FieldIdx) -> &FieldDef {
        &self.fields[field]
    }
}

#[derive(Debug, Hash)]
pub struct FieldDef {
    pub def: DefId,
    pub symbol: Symbol
}

index_vec::define_index_type! {
    pub struct FieldIdx = u32;
    IMPL_RAW_CONVERSIONS = true;
}

#[derive(Clone, Copy, clyde_macros::Recursible)]
pub struct Signature<'tcx> {
    pub returns: Ty<'tcx>,
    pub params: &'tcx [Param<'tcx>],
    #[non_recursible]
    pub name: Symbol,
    #[non_recursible]
    pub has_errors: bool,
    #[non_recursible]
    pub intrinsic: bool
}

#[derive(Clone, Copy, clyde_macros::Recursible)]
pub struct Param<'tcx> {
    #[non_recursible]
    pub name: Symbol,
    pub ty: Ty<'tcx>,
    #[non_recursible]
    pub node_id: NodeId
}


#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum ScalarKind {
    Signed,
    Unsigned,
    // FIXME: ScalarInt should not store floats at all
    Float
}

#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq)]
#[repr(packed)]
pub struct ScalarInt {
    pub data: u64,
    pub size: u8,
    pub kind: ScalarKind,
}

impl ScalarInt {
    pub fn from_signed_integer(data: i64, kind: Integer) -> Self {
        let (data, size) = match kind {
            Integer::I8 => (data as i8 as u64, 1),
            Integer::I16 => (data as i16 as u64, 2),
            Integer::I32 => (data as i32 as u64, 4),
            Integer::I64 => (data as i64 as u64, 8),
            Integer::ISize => unreachable!()
        };

        ScalarInt { size, data, kind: ScalarKind::Signed }
    }

    pub fn from_unsigned_integer(data: u64, kind: Integer) -> Self {
        let (data, size) = match kind {
            Integer::I8 => (data as u8 as u64, 1),
            Integer::I16 => (data as u16 as u64, 2),
            Integer::I32 => (data as u32 as u64, 4),
            Integer::I64 => (data, 8),
            Integer::ISize => unreachable!()
        };

        ScalarInt { size, data, kind: ScalarKind::Unsigned }
    }

    pub fn from_float(data: f64, kind: Float) -> Self {
        let (data, size) = match kind {
            Float::F32 => (unsafe { std::mem::transmute(data as f64) }, 4),
            Float::F64 => (unsafe { std::mem::transmute(data) }, 8),
        };

        ScalarInt { size, data, kind: ScalarKind::Float }
    }

    pub fn from_size(provider: &impl DataLayoutExt, data: u64) -> Self {
        Self::from_unsigned_integer(data, Integer::ISize.normalize(provider))
    }

    pub fn try_to_target_usize<'tcx>(&self, tcx: TyCtxt<'tcx>) -> Option<u64> {
        self.to_bits(tcx.data_layout().ptr_size)
    }

    pub fn to_bits(&self, size: Size) -> Option<u64> {
        if size.in_bytes != self.size as u64 {
            return None
        }
        return Some(self.data)
    }

    pub fn as_unsigned(&self) -> u64 {
        self.data
    }

    pub fn as_signed(&self) -> i64 {
        let size = Size::from_bytes(self.size as u8);
        size.sign_extend(self.data)
    }

    pub fn as_float(&self) -> f64 {
        unsafe { std::mem::transmute(self.data) }
    }
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub enum ConstKind<'tcx> {
    Value(ScalarInt),
    Param(Symbol, usize),
    Infer(PhantomData<&'tcx ()>),
    Err
}

#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq)]
pub struct Const<'tcx>(pub &'tcx ConstKind<'tcx>);

impl<'tcx> Const<'tcx> {
    pub fn new_error(tcx: TyCtxt<'tcx>) -> Self {
        tcx.intern_const(ConstKind::Err)
    }

    pub fn try_to_target_usize(&self, tcx: TyCtxt<'tcx>) -> Option<u64> {
        if let Const(ConstKind::Value(scalar)) = self {
            return scalar.try_to_target_usize(tcx);
        }
        None
    }
}

impl<'tcx> std::fmt::Display for Const<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        context::with_tcx(|tcx| {
            let tcx = *tcx.unwrap();
            PrettyPrinter::print_to_formatter(tcx, f, |p| {
                self.lift(tcx).unwrap().print(p)
            })
        })
    }
}

#[derive(Debug)]
pub struct Enum<'tcx> {
    pub def: DefId,
    pub name: Symbol,
    pub representation: Option<Ty<'tcx>>,
    pub variants: IndexVec<VariantIdx, Variant>,
}

index_vec::define_index_type! {
    pub struct VariantIdx = u32;
    IMPL_RAW_CONVERSIONS = true;
}

#[derive(Debug)]
pub struct Variant {
    pub name: Symbol,
    pub def: DefId,
    pub discriminant: Discriminant
}

#[derive(Debug)]
pub enum Discriminant {
    Explicit { def: DefId },
    Relative { offset: u32 },
}

impl<'tcx> Enum<'tcx> {
    pub fn new(
        def: DefId,
        name: Symbol,
        representation: Option<Ty<'tcx>>,
        variants: IndexVec<VariantIdx, Variant>,
    ) -> Self {
        Self { def, name, representation, variants }
    }
}

impl<'tcx> std::hash::Hash for Enum<'tcx> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.def.hash(state);
        self.name.hash(state);
    }
}

impl<'tcx> PartialEq for Enum<'tcx> {
    fn eq(&self, other: &Self) -> bool {
        self.def == other.def
    }
}

impl<'tcx> Eq for Enum<'tcx> {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ParamTy {
    pub index: usize,
    pub symbol: Symbol
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub enum TyKind<'tcx> {
    Bool,
    Void,
    Char,
    String,
    Int(Integer, bool),
    Float(Float),
    Adt(AdtDef<'tcx>, &'tcx GenericArgs<'tcx>),
    Enum(Enum<'tcx>),
    Refrence(Ty<'tcx>),
    Range(Ty<'tcx>, bool),
    Slice(Ty<'tcx>),
    Array(Ty<'tcx>, Const<'tcx>),
    Tuple(&'tcx [Ty<'tcx>]),
    DynamicArray(Ty<'tcx>),
    Function(DefId, &'tcx GenericArgs<'tcx>),
    Param(ParamTy),
    Never,
    Err
}

#[derive(Debug, Clone, Copy, Hash)]
pub struct Ty<'tcx>(pub &'tcx TyKind<'tcx>);

impl<'tcx> PartialEq for Ty<'tcx> {
    fn eq(&self, other: &Self) -> bool {
        if let Ty(TyKind::Never | TyKind::Err) = self {
            return true;
        }
        if let Ty(TyKind::Never | TyKind::Err) = other {
            return true;
        }
        std::ptr::eq(self.0, other.0)
    }
}

impl<'tcx> Eq for Ty<'tcx> {}

impl<'tcx> std::fmt::Display for Ty<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        context::with_tcx(|tcx| {
            let tcx = *tcx.unwrap();
            PrettyPrinter::print_to_formatter(tcx, f, |p| {
                self.lift(tcx).unwrap().print(p)
            })
        })
    }
}

impl<'tcx> FromCycleError<'tcx> for Ty<'tcx> {
    fn from_cycle_error(tcx: TyCtxt<'tcx>) -> Self {
        Ty::new_error(tcx)
    }
}

impl<'tcx> Ty<'tcx> {
    pub fn new_array(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, cnst: Const<'tcx>) -> Ty<'tcx> {
        tcx.intern_ty(TyKind::Array(ty, cnst))
    }

    pub fn new_slice(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Ty<'tcx> {
        tcx.intern_ty(TyKind::Slice(ty))
    }

    pub fn new_dyn_array(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Ty<'tcx> {
        tcx.intern_ty(TyKind::DynamicArray(ty))
    }

    pub fn new_refrence(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Ty<'tcx> {
        tcx.intern_ty(TyKind::Refrence(ty))
    }

    pub fn new_error(tcx: TyCtxt<'tcx>) -> Ty<'tcx> {
        tcx.intern_ty(TyKind::Err)
    }

    pub fn new_int(tcx: TyCtxt<'tcx>, int: Integer, signed: bool) -> Ty<'tcx> {
        tcx.intern_ty(TyKind::Int(int, signed))
    }

    pub fn new_float(tcx: TyCtxt<'tcx>, float: Float) -> Ty<'tcx> {
        tcx.intern_ty(TyKind::Float(float))
    }

    pub fn new_enum(tcx: TyCtxt<'tcx>, enm: Enum<'tcx>) -> Ty<'tcx> {
        tcx.intern_ty(TyKind::Enum(enm))
    }

    pub fn new_adt(tcx: TyCtxt<'tcx>, adt: AdtDef<'tcx>) -> Ty<'tcx> {
        tcx.intern_ty(TyKind::Adt(adt, adt.def().normalized_generics(tcx)))
    }

    pub fn new_function(tcx: TyCtxt<'tcx>, def: DefId) -> Ty<'tcx> {
        tcx.intern_ty(TyKind::Function(def, def.normalized_generics(tcx)))
    }

    pub fn new_range(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, inclusive: bool) -> Ty<'tcx> {
        tcx.intern_ty(TyKind::Range(ty, inclusive))
    }

    pub fn new_tuple(tcx: TyCtxt<'tcx>, tys: &'tcx [Ty<'tcx>]) -> Ty<'tcx> {
        tcx.intern_ty(TyKind::Tuple(tys))
    }

    pub fn new_param(tcx: TyCtxt<'tcx>, symbol: Symbol, index: usize) -> Ty<'tcx> {
        tcx.intern_ty(TyKind::Param(ParamTy {
            symbol,
            index
        }))
    }

    /// Searches slice types for bendable types (Never, Err)
    /// while preferring Err over Never
    pub fn with_bendable(types: &[Ty<'tcx>]) -> Option<Ty<'tcx>> {
        let mut found = None;
        for ty in types {
            if let Ty(TyKind::Err) = ty {
                return Some(*ty);
            } else if let Ty(TyKind::Never) = ty {
                found = Some(*ty);
            }
        }

        return found;
    }

    /// Searches slice types for bendable types (Never, Err)
    /// while preferring Err and rejecting Never
    pub fn with_non_bendable(types: &[Ty<'tcx>]) -> Option<Ty<'tcx>> {
        let mut never = None;
        for ty in types {
            if let Ty(TyKind::Err) = ty {
                return Some(*ty);
            } else if let Ty(TyKind::Never) = ty {
                never = Some(*ty);
                continue;
            }
            return Some(*ty);
        }
        never
    }

    pub fn is_incomplete(&self) -> bool {
        match self {
            Ty(TyKind::Array(_, Const(ConstKind::Infer(..)))) => true,
            _ => false
        }
    }

}

impl Symbol {
    pub fn is_primitive_ty<'tcx>(&self) -> bool {
        match *self {
            sym::bool => true,
            sym::void => true,
            sym::byte => true,
            sym::sbyte => true,
            sym::short => true,
            sym::ushort => true,
            sym::int => true,
            sym::uint => true,
            sym::long => true,
            sym::ulong => true,
            sym::nint => true,
            sym::nuint => true,
            sym::char => true,
            sym::string => true,
            sym::float => true,
            sym::double => true,
            _ => false
        }
    }

    pub fn get_primitive_ty<'tcx>(&self, tcx: TyCtxt<'tcx>) -> Option<Ty<'tcx>> {
        match *self {
            sym::bool => Some(tcx.basic_types.bool),
            sym::void => Some(tcx.basic_types.void),
            sym::byte => Some(tcx.basic_types.byte),
            sym::sbyte => Some(tcx.basic_types.sbyte),
            sym::short => Some(tcx.basic_types.short),
            sym::ushort => Some(tcx.basic_types.ushort),
            sym::int => Some(tcx.basic_types.int),
            sym::uint => Some(tcx.basic_types.uint),
            sym::long => Some(tcx.basic_types.long),
            sym::ulong => Some(tcx.basic_types.ulong),
            sym::nint => Some(tcx.basic_types.nint),
            sym::nuint => Some(tcx.basic_types.nuint),
            sym::char => Some(tcx.basic_types.char),
            sym::string => Some(tcx.basic_types.string),
            sym::float => Some(tcx.basic_types.float),
            sym::double => Some(tcx.basic_types.double),

            _ => None
        }
    }
}

#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq)]
pub enum Integer {
    I8,
    I16,
    I32,
    I64,
    ISize
}

impl Integer {
    pub fn fit_signed(value: i128) -> Option<Self> {
        use Integer::*;
        match value {
            -0x0000_0000_0000_0080..=0x0000_0000_0000_007f => Some(I8),
            -0x0000_0000_0000_8000..=0x0000_0000_0000_7fff => Some(I16),
            -0x0000_0000_8000_0000..=0x0000_0000_7fff_ffff => Some(I32),
            -0x8000_0000_0000_0000..=0x7fff_ffff_ffff_ffff => Some(I64),
            _ => None,
        }

    }

    pub fn fit_unsigned(value: u64) -> Self {
        use Integer::*;
        match value {
            0..=0x0000_00ff => I8,
            0..=0x0000_ffff => I16,
            0..=0xffff_ffff => I32,
            _ => I64
        }
    }

    pub fn to_symbol(&self, signedness: bool) -> Symbol {
        use Integer::*;
        match (self, signedness) {
            (I8, false) => sym::byte,
            (I16, false) => sym::ushort,
            (I32, false) => sym::uint,
            (I64, false) => sym::ulong,
            (ISize, false) => sym::nuint,

            (I8, true) => sym::sbyte,
            (I16, true) => sym::short,
            (I32, true) => sym::int,
            (I64, true) => sym::long,
            (ISize, true) => sym::nint,
        }
    }

}

#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq)]
pub enum Float {
    F32,
    F64
}

pub struct BasicTypes<'tcx> {
    pub bool: Ty<'tcx>,
    pub void: Ty<'tcx>,
    pub byte: Ty<'tcx>,
    pub sbyte: Ty<'tcx>,
    pub short: Ty<'tcx>,
    pub ushort: Ty<'tcx>,
    pub int: Ty<'tcx>,
    pub uint: Ty<'tcx>,
    pub long: Ty<'tcx>,
    pub ulong: Ty<'tcx>,
    pub nint: Ty<'tcx>,
    pub nuint: Ty<'tcx>,
    pub float: Ty<'tcx>,
    pub double: Ty<'tcx>,
    pub char: Ty<'tcx>,
    pub string: Ty<'tcx>,
    pub never: Ty<'tcx>,
}

impl<'tcx> BasicTypes<'tcx> {
    pub fn alloc(interners: &Interners<'tcx>) -> Self {
        use Integer::*;
        use Float::*;
        use TyKind::{Bool, Char, String, Void, Never, Int};
        let mk = |ty| interners.intern_ty(ty);

        Self {
            bool: mk(Bool),
            void: mk(Void),
            char: mk(Char),
            string: mk(String),
            never: mk(Never),
            
            byte: mk(Int(I8, false)),
            sbyte: mk(Int(I8, true)),
            short: mk(Int(I16, true)),
            ushort: mk(Int(I16, false)),
            int: mk(Int(I32, true)),
            uint: mk(Int(I32, false)),
            long: mk(Int(I64, true)),
            ulong: mk(Int(I64, false)),
            nint: mk(Int(ISize, true)),
            nuint: mk(Int(ISize, false)),

            float: mk(TyKind::Float(F32)),
            double: mk(TyKind::Float(F64)),
        }
    }
}

impl<'tcx> Interners<'tcx> {
    fn intern_ty(&self, kind: TyKind<'tcx>) -> Ty<'tcx> {
        use crate::context::InternerExt;
        let interner = &self.tys;
        Ty(interner.intern(kind, |kind| {
            self.arena.alloc(kind)
        }))
    }
}

