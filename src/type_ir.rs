use std::ops::Deref;

use index_vec::IndexVec;
use num_traits::{Num, PrimInt, ToPrimitive};

use crate::{context::{FromCycleError, Interners, TyCtxt}, diagnostics::Message, syntax::{ast::{self, DefId, NodeId}, lexer::Span, symbol::{sym, Symbol}}, target::{DataLayoutExt, TargetDataLayout}};

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
    Enum(Enum),
    Union,
}

impl AdtKind {
    pub fn def(&self) -> DefId {
        match self {
            AdtKind::Struct(strct) => strct.def,
            AdtKind::Enum(enm) => enm.def,
            AdtKind::Union => todo!()
        }
    }

    pub fn name(&self) -> Symbol {
        match self {
            AdtKind::Struct(strct) => strct.name,
            AdtKind::Enum(enm) => enm.name,
            AdtKind::Union => todo!()
        }
    }

    pub fn kind(&self) -> &'static str {
        match self {
            AdtKind::Struct(..) => "struct",
            AdtKind::Enum(..) => "enum",
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
pub struct Enum {
    pub def: DefId,
    pub name: Symbol,
    variants: IndexVec<VariantIdx, VariantDef>,
}

impl Enum {
    pub fn new(
        def: DefId,
        name: Symbol,
        variants: IndexVec<VariantIdx, VariantDef>,
    ) -> Self {
        Self { def, name, variants }
    }
}

#[derive(Debug, Hash)]
pub struct VariantDef {
    pub def: DefId,
    pub symbol: Symbol
}

index_vec::define_index_type! {
    pub struct VariantIdx = u32;
    IMPL_RAW_CONVERSIONS = true;
}

#[derive(Debug, Hash)]
pub struct Struct {
    pub def: DefId,
    pub name: Symbol,
    fields: IndexVec<FieldIdx, FieldDef>,
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

#[derive(Clone, Copy)]
pub struct Signature<'tcx> {
    pub returns: Ty<'tcx>,
    pub params: &'tcx [Param<'tcx>],
    pub name: Symbol,
    pub has_errors: bool
}

#[derive(Clone, Copy)]
pub struct Param<'tcx> {
    pub name: Symbol,
    pub ty: Ty<'tcx>,
    pub node_id: NodeId
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct Scalar {
    size: usize,
    data: u128
}

impl Scalar {
    pub fn from_number<N: Num + ToPrimitive>(number: N) -> Self {
        let size = std::mem::size_of::<N>();
        Scalar { size, data: number.to_u128().unwrap() }
    }
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub enum ValTree<'tcx> {
    Scalar(Scalar),
    Branch(&'tcx [ValTree<'tcx>])
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub enum ConstInner<'tcx> {
    Value(Ty<'tcx>, ValTree<'tcx>),
    Placeholder,
    Err {
        msg: String,
        span: Span
    }
}

#[derive(Hash, Clone, Copy, PartialEq, Eq)]
pub struct Const<'tcx>(pub &'tcx ConstInner<'tcx>);

impl<'tcx> Const<'tcx> {
    pub fn void_value(tcx: TyCtxt<'tcx>) -> Const<'tcx> {
        let void = tcx.basic_types.void;
        let value = ValTree::Branch(&[]);
        tcx.intern_const(ConstInner::Value(void, value))
    }

    pub fn from_definition(tcx: TyCtxt<'tcx>, def_id: DefId) -> Const<'tcx> {
        let node = tcx.node_by_def_id(def_id);

        let body = node.body()
            .expect("const should have a body");

        let ty = tcx.type_of(def_id);
        match Self::try_val_from_simple_expr(tcx, ty, body.body) {
            Some(v) => v,
            None => tcx.intern_const(ConstInner::Err {
                msg: "Sry, propper const evaluation is not a priority".to_string(),
                span: body.body.span
            })
        }
    }

    fn int_to_val(tcx: TyCtxt<'tcx>, int: ast::Integer, ty: Ty<'tcx>) -> Result<ConstInner<'tcx>, String> {
        let min_int = if int.signed {
            let Some(int) = Integer::fit_signed(-(int.value as i128)) else {
                return Err(format!("{} does not fit into signed long", int.value));
            };
            int
        } else {
            Integer::fit_unsigned(int.value)
        };

        if let Ty(TyKind::Int(integer, signed)) = ty && *signed | !int.signed {
            let min_int = if *signed {
                Integer::fit_signed((int.value as i128) * if int.signed { -1 } else { 1 }).map_or(128, |i| i.size(&tcx))
            } else {
                Integer::fit_unsigned(int.value).size(&tcx)
            };

            if integer.size(&tcx) >= min_int {
                let scalar = Scalar {
                    size: integer.size(&tcx),
                    data: int.value as u128
                };
                return Ok(ConstInner::Value(ty, ValTree::Scalar(scalar)));
            }
        }

        Err(format!("mismatched types: expected {ty}, found {}", Ty::new_int(tcx, min_int, int.signed)))
    }

    fn literal_to_ty(tcx: TyCtxt<'tcx>, literal: &ast::Literal) -> Ty<'tcx> {
        match literal {
            ast::Literal::String(..) => 
                tcx.basic_types.string,
            ast::Literal::Boolean(..) =>
                tcx.basic_types.bool,
            ast::Literal::Char(..) =>
                tcx.basic_types.char,
            ast::Literal::Integer(..) =>
                tcx.basic_types.int,
            ast::Literal::Floating(..) => todo!(),
            ast::Literal::Null => panic!("can't infer type from null")
        }
    }

    fn try_val_from_simple_expr(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, expr: &'tcx ast::Expr) -> Option<Self> {
        let ast::ExprKind::Literal(literal) = &expr.kind else {
            return None;
        };
        match Self::from_literal(tcx, ty, literal) {
            Ok(cnst) => Some(cnst),
            Err(msg) => Some(tcx.intern_const(ConstInner::Err {
                msg, span: expr.span
            }))
        }
    }

    pub fn from_literal(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, literal: &ast::Literal) -> Result<Self, String> {
        let inner = match (ty.0, literal) {
            (TyKind::String, ast::Literal::String(str)) =>  {
                let mut slice = Vec::new();
                for byte in str.as_bytes() {
                    let val = Scalar::from_number(*byte);
                    slice.push(ValTree::Scalar(val));
                }

                let slice = slice.into_boxed_slice();
                let slice: &[ValTree] = tcx.arena.alloc(slice);

                ConstInner::Value(ty, ValTree::Branch(slice))
            }
            (TyKind::Bool, ast::Literal::Boolean(bool)) =>
                ConstInner::Value(ty, ValTree::Scalar(Scalar::from_number(*bool as u8))),
            (TyKind::Char, ast::Literal::Char(char)) =>
                ConstInner::Value(ty, ValTree::Scalar(Scalar::from_number(*char as u32))),
            (TyKind::Int(..), ast::Literal::Integer(int)) =>
                Self::int_to_val(tcx, *int, ty)?,
            (TyKind::Refrence(..), ast::Literal::Null) =>
                // FIXME: `as usize` here will make the size of the scalar depend on the size
                // of the architecture the compiler was compiled on, not the target usize
                ConstInner::Value(ty, ValTree::Scalar(Scalar::from_number(0 as usize))),
            (_, ast::Literal::Null) =>
                return Err(format!("non refrence-type {ty} cannot be null")),
            _ =>
                return Err(format!("mismatched types: expected {ty}, found {}", Self::literal_to_ty(tcx, literal))),
        };

        Ok(tcx.intern_const(inner))
    }

    pub fn from_bool(tcx: TyCtxt<'tcx>, value: bool) -> Const<'tcx> {
        tcx.intern_const(ConstInner::Value(tcx.basic_types.bool, ValTree::Scalar(Scalar::from_number(value as u8))))
    }

    pub fn try_as_usize(&self) -> Option<usize> {
        match self.0 {
            ConstInner::Placeholder | ConstInner::Err { .. } => None,
            ConstInner::Value(ty, val) => {
                let Ty(TyKind::Int(Integer::ISize, false)) = ty else {
                    return None;
                };
                let ValTree::Scalar(Scalar { size: 8, data }) = val else {
                    unreachable!("const nuint is not stored as a scalar of size 8");
                };
                Some(*data as usize)
            }
        }
    }
}

impl<'tcx> std::fmt::Debug for Const<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        /*let scalar = if let ValTree::Scalar(scalar) = value {
            Some(scalar.data)
        } else {
            None
        };*/
        match self.0 {
            ConstInner::Value(Ty(TyKind::Void), _) =>
                f.write_str("<empty>"),
            ConstInner::Value(Ty(TyKind::String), _) =>
                f.write_str("<string>"),
            ConstInner::Value(Ty(TyKind::Float(..)), _) =>
                todo!(),
            ConstInner::Value(Ty(TyKind::Bool), ValTree::Scalar(scalar)) =>
                write!(f, "{}_bool", scalar.data != 0),
            ConstInner::Value(Ty(TyKind::Char), ValTree::Scalar(scalar)) =>
                write!(f, "{}_char", char::from_u32(scalar.data as u32).unwrap()),
            ConstInner::Value(ty @ Ty(TyKind::Int(_, true)), ValTree::Scalar(scalar)) =>
                write!(f, "{}_{ty}", scalar.data as i64),
            ConstInner::Value(ty @ Ty(TyKind::Int(_, false)), ValTree::Scalar(scalar)) =>
                write!(f, "{}_{ty}", scalar.data as u64),
            ConstInner::Value(..) => f.write_str("<value>"),
            ConstInner::Placeholder => f.write_str("_"),
            ConstInner::Err { .. } => f.write_str("<err>"),
        }
    }
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub enum TyKind<'tcx> {
    Bool,
    Void,
    Char,
    String,
    Int(Integer, bool),
    Float(Float),
    Adt(AdtDef<'tcx>),
    Refrence(Ty<'tcx>),
    Range(Ty<'tcx>, bool),
    Slice(Ty<'tcx>),
    Array(Ty<'tcx>, Const<'tcx>),
    Tuple(&'tcx [Ty<'tcx>]),
    DynamicArray(Ty<'tcx>),
    Function(DefId),
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
        match self.0 {
            TyKind::Never => write!(f, "never"),
            TyKind::Int(integer, signed) => {
                let sym = integer.to_symbol(*signed);
                f.write_str(sym.get())
            },
            TyKind::Bool => f.write_str("bool"),
            TyKind::Void => f.write_str("void"),
            TyKind::Char => f.write_str("char"),
            TyKind::String => f.write_str("string"),
            TyKind::Float(Float::F32) => f.write_str("float"),
            TyKind::Float(Float::F64) => f.write_str("double"),
            TyKind::Adt(adt) => f.write_str(adt.name().get()),
            TyKind::Refrence(ty) => write!(f, "{ty}*"),
            TyKind::Slice(ty) => write!(f, "{ty}[]"),
            TyKind::Array(ty, _) => write!(f, "{ty}[_]"),
            TyKind::DynamicArray(ty) => write!(f, "{ty}[..]"),
            TyKind::Function(_) => write!(f, "function"),
            TyKind::Range(ty, _) => write!(f, "Range<{ty}>"),
            TyKind::Tuple(tys) => {
                f.write_str("tuple<")?;
                for (idx, ty) in tys.iter().enumerate() {
                    write!(f, "{ty}")?;
                    if idx != tys.len() - 1 {        
                        f.write_str(", ")?;
                    }
                }
                f.write_str(">")?;
                Ok(())
            }
            TyKind::Err => write!(f, "Err"),
        }
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

    pub fn new_adt(tcx: TyCtxt<'tcx>, adt: AdtDef<'tcx>) -> Ty<'tcx> {
        tcx.intern_ty(TyKind::Adt(adt))
    }

    pub fn new_function(tcx: TyCtxt<'tcx>, def: DefId) -> Ty<'tcx> {
        tcx.intern_ty(TyKind::Function(def))
    }

    pub fn new_range(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, inclusive: bool) -> Ty<'tcx> {
        tcx.intern_ty(TyKind::Range(ty, inclusive))
    }

    pub fn new_tuple(tcx: TyCtxt<'tcx>, tys: &'tcx [Ty<'tcx>]) -> Ty<'tcx> {
        tcx.intern_ty(TyKind::Tuple(tys))
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
            Ty(TyKind::Array(_, Const(ConstInner::Placeholder))) => true,
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

    pub fn size(&self, provider: &impl DataLayoutExt) -> usize {
        let data_layout = provider.data_layout();
        use Integer::*;
        match self {
            I8 => 1,
            I16 => 2,
            I32 => 4,
            I64 => 8,
            ISize => data_layout.ptr_size.in_bytes as usize,
        }
    }

    pub fn align(&self, provider: &impl DataLayoutExt) -> LLVMAlign {
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

impl Float {
    pub fn size(&self) -> usize {
        match self {
            Float::F32 => 4,
            Float::F64 => 8,
        }
    }

    pub fn align(&self, provider: &impl DataLayoutExt) -> LLVMAlign {
        let data_layout = provider.data_layout();
        match self {
            Float::F32 => data_layout.f32_align,
            Float::F64 => data_layout.f64_align,
        }
    }
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

#[derive(Debug, Clone, Copy)]
pub enum Endianness {
    Little, Big
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Align {
    pow2: u8
}

impl Align {
    const ONE: Align = Align::from_bytes(1);
    const LLVM_MAX_ALIGN: u32 = 29;

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

/// A special LLVM version of an `Align` containing one `abi` and one `pref` alignment
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LLVMAlign {
    pub abi: Align,
    pub pref: Align
}

impl LLVMAlign {
    pub const fn from_bits(bits: u64) -> Self {
        Self {
            abi: Align::from_bits(bits),
            pref: Align::from_bits(bits),
        }
    }

    pub const fn from_align(align: Align) -> Self {
        Self {
            abi: align,
            pref: align,
        } 
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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
pub enum BackendScalar {
    Int(Integer, bool),
    Float(Float),
    Pointer
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BackendRepr {
    Scalar(BackendScalar),
    ScalarPair(BackendScalar, BackendScalar),
    Memory
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct LayoutData {
    pub size: Size,
    pub align: LLVMAlign,
    pub fields: Fields,
    pub repr: BackendRepr
}

#[derive(Debug, Clone, Copy)]
pub struct TypeLayout<'tcx>(pub &'tcx LayoutData);

impl<'tcx> std::ops::Deref for TypeLayout<'tcx> {
    type Target = LayoutData;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

impl<'tcx> TypeLayout<'tcx> {
    fn new(tcx: TyCtxt<'tcx>, size: Size, align: LLVMAlign, fields: Fields, repr: BackendRepr) -> Self {
        tcx.intern_layout(LayoutData { size, align, fields, repr })
    }
}

#[derive(Clone, Copy)]
pub enum LayoutError {
    /// The Ty was erroneous to begin with (TyKind::Error), no sensible layout can be computed
    Erroneous,
    /// The Ty's layout is cyclic: Ty contains itself without any indirection
    Cyclic
}

impl<'tcx> FromCycleError<'tcx> for Result<TypeLayout<'tcx>, LayoutError> {
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

    fn layout_for_array_like(&self, dynamic_sized: bool) -> TypeLayout<'tcx> {
        let data_layout = self.data_layout();
        let align = data_layout.ptr_align;
        let ptr_size = data_layout.ptr_size;

        let nuint = BackendScalar::Int(Integer::ISize.normalize(self), false);

        let mut fields = IndexVec::new();
        fields.push(0);
        fields.push(ptr_size.in_bytes);
        if dynamic_sized {
            fields.push(ptr_size.in_bytes * 2);
        }


        TypeLayout::new(
            self.tcx,
            Size::from_bytes(ptr_size.in_bytes * (2 + dynamic_sized as u64)),
            align,
            Fields::Struct { fields },
            if !dynamic_sized {
                BackendRepr::ScalarPair(BackendScalar::Pointer, nuint)
            } else {
                BackendRepr::Memory
            }
        )
    }

    fn layout_for_integer(&self, integer: Integer, signedness: bool) -> TypeLayout<'tcx> {
        let size = integer.size(self);
        let align = integer.align(self);
        TypeLayout::new(
            self.tcx,
            Size::from_bytes(size),
            align,
            Fields::Scalar,
            BackendRepr::Scalar(BackendScalar::Int(integer, signedness))
        )
    }

    fn layout_for_float(&self, float: Float) -> TypeLayout<'tcx> {
        let size = float.size();
        let align = float.align(self);
        TypeLayout::new(
            self.tcx,
            Size::from_bytes(size),
            align,
            Fields::Scalar,
            BackendRepr::Scalar(BackendScalar::Float(float))
        )
    }

    fn layout_for_struct(&self, fields: IndexVec<FieldIdx, TypeLayout<'tcx>>) -> TypeLayout<'tcx> {
        let mut abi = Align::ONE;
        let mut offset = 0;
        let mut offsets = IndexVec::new();
        let mut size = 0;
        for field in &fields {
            size += field.size.in_bytes;
            abi = std::cmp::max(abi, field.align.abi);
            if offset % field.align.abi.in_bytes() != 0 {
                offset = align_up(offset, field.align.abi);
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


        TypeLayout::new(
            self.tcx,
            Size::from_bytes(size),
            LLVMAlign::from_align(abi),
            Fields::Struct { fields: offsets },
            repr
        )
    }

    fn layout_for_array(&self, ty: Ty<'tcx>, count: u64) -> Result<TypeLayout<'tcx>, LayoutError> {
        let layout = match self.tcx.layout_of(ty) {
            Ok(layout) => layout,
            Err(LayoutError::Cyclic) => {
                // A type refrencing itself like this should only be possible using type aliases 
                // (NOTE: in the future maybe through compile-time meta programming)
                // TODO: once type aliases become a thing: unintern the Ty IR into it's AST Node
                todo!("type alias cyclic types");
            }
            err @ Err(_) => return err
        };
        let align = layout.align;
        Ok(TypeLayout::new(
            self.tcx,
            Size { in_bytes: count * layout.size.in_bytes },
            align,
            Fields::Array { stride: layout.size.in_bytes, count },
            BackendRepr::Memory
        ))
    }

    fn calculate_layout_for_ty(&self, ty: Ty<'tcx>) -> Result<TypeLayout<'tcx>, LayoutError> {
        let layout = match ty {
            Ty(TyKind::Void) | Ty(TyKind::Never) =>
                TypeLayout::new(
                    self.tcx,
                    Size::from_bytes(0),
                    LLVMAlign::from_align(Align::ONE),
                    Fields::Struct { fields: IndexVec::new() },
                    BackendRepr::Memory
                ),
            Ty(TyKind::Bool) =>
                self.tcx.layout_of(self.tcx.basic_types.byte)?,
            Ty(TyKind::Char) =>
                self.tcx.layout_of(self.tcx.basic_types.uint)?,
            Ty(TyKind::String) =>
                self.layout_for_array_like(false),

            Ty(TyKind::Int(integer, signedness)) =>
                self.layout_for_integer(*integer, *signedness),
            Ty(TyKind::Float(float)) =>
                self.layout_for_float(*float),
            Ty(TyKind::Adt(adt)) => {
                match adt {
                    AdtDef(AdtKind::Struct(strct)) => {
                        let mut fields = IndexVec::new();
                        for field in strct.fields.iter() {
                            let layout = match self.tcx.layout_of(self.tcx.type_of(field.def)) {
                                Ok(layout) => layout,
                                err @ Err(LayoutError::Cyclic) => {
                                    let ast::Node::Item(item) = self.tcx.node_by_def_id(strct.def) else { unreachable!() };
                                    let ast::Node::FieldDef(def) = self.tcx.node_by_def_id(field.def) else { unreachable!() };
                                    self.report_cycle_error(item.ident().span, def.ty.span, format_args!("struct `{}`", strct.name.get()));
                                    return err;
                                }
                                err @ Err(_) => return err
                            };
                            fields.push(layout); 
                        }
                        self.layout_for_struct(fields)
                    }
                    AdtDef(AdtKind::Enum(_enm)) => todo!(),
                    AdtDef(AdtKind::Union) => todo!(),
                }
            }
            Ty(TyKind::Refrence(..)) => {
                let data_layout = self.data_layout();
                TypeLayout::new(
                    self.tcx,
                    data_layout.ptr_size,
                    data_layout.ptr_align,
                    Fields::Scalar,
                    BackendRepr::Scalar(BackendScalar::Pointer)
                )
            }
            Ty(TyKind::Range(..)) => todo!(),
            Ty(TyKind::Slice(_)) =>
                self.layout_for_array_like(false),
            Ty(TyKind::Array(base, count)) =>
                self.layout_for_array(*base, count.try_as_usize().unwrap() as u64)?,
            Ty(TyKind::Tuple(tys)) => {
                let mut fields = IndexVec::new();
                for ty in tys.iter() {
                    let layout = match self.tcx.layout_of(*ty) {
                        Ok(layout) => layout,
                        Err(LayoutError::Cyclic) => {
                            // A type refrencing itself like this should only be possible using type aliases 
                            // (NOTE: in the future maybe through compile-time meta programming)
                            // TODO: once type aliases become a thing: unintern the Ty IR into it's AST Node
                            todo!("type alias cyclic types");
                        }
                        err @ Err(_) => return err
                    };
                    fields.push(layout); 
                }
                self.layout_for_struct(fields)
            },
            Ty(TyKind::DynamicArray(_)) =>
                self.layout_for_array_like(true),
            Ty(TyKind::Function(..)) => 
                TypeLayout::new(
                    self.tcx,
                    Size::from_bytes(0),
                    LLVMAlign::from_align(Align::ONE),
                    Fields::Struct { fields: IndexVec::new() },
                    BackendRepr::Memory
                ),
            Ty(TyKind::Err) => return Err(LayoutError::Erroneous),
        };
        Ok(layout)
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

pub fn layout_of<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Result<TypeLayout<'tcx>, LayoutError> {
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
