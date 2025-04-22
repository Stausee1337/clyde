use std::ops::Deref;

use index_vec::IndexVec;
use num_traits::{Num, ToPrimitive};

use crate::{ast::{self, DefId, NodeId}, context::{Interners, TyCtxt}, lexer::Span, symbol::{sym, Symbol}};

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
                Integer::fit_signed((int.value as i128) * if int.signed { -1 } else { 1 }).map_or(128, |i| i.size())
            } else {
                Integer::fit_unsigned(int.value).size()
            };

            if integer.size() >= min_int {
                let scalar = Scalar {
                    size: integer.size(),
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
    Tuple(Vec<Ty<'tcx>>),
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

    pub fn new_tuple(tcx: TyCtxt<'tcx>, tys: Vec<Ty<'tcx>>) -> Ty<'tcx> {
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

    pub fn size(&self) -> usize {
        use Integer::*;
        match self {
            I8 => 1,
            I16 => 2,
            I32 => 4,
            I64 => 8,
            ISize => 8, // FIXME: use backend info to fill this gap
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

