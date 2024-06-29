use std::{mem::transmute, ops::Deref, fmt::Write, collections::HashSet};

use bumpalo::Bump;
use bitflags::bitflags;

use crate::{ast::{DefId, NodeId}, symbol::Symbol, context::{SharedHashMap, TyCtxt, Interner, self}, diagnostics::DiagnosticsData};


#[derive(Debug, Hash)]
#[repr(u32)]
pub enum AdtKind {
    Enum,
    Struct,
    Union,
}
macro_rules! interners {
    ($($interner:ident : $fn:ident($ty:ty) -> $ret:ident;)*) => {
        $(
            impl<'tcx> TyCtxt<'tcx> {
                pub fn $fn(&self, value: $ty) -> $ret<'tcx> {
                    $ret(self.interners.$interner.intern(value, |value| {
                        self.interners.alloc(value)
                    }))
                }
            }
        )*
    };
}

interners! {
    adt_defs: mk_adt_from_inner(AdtDefInner) -> AdtDef;
    consts: mk_const_from_inner(ConstInner<'tcx>) -> Const;
}

#[derive(Default)]
pub struct CtxtInterners<'tcx> {
    arena: Bump,
    types: SharedHashMap<&'tcx TyKind<'tcx>>,
    adt_defs: SharedHashMap<&'tcx AdtDefInner>,
    consts: SharedHashMap<&'tcx ConstInner<'tcx>>,
}

impl<'tcx> CtxtInterners<'tcx> {
    pub fn alloc<'r, T>(&self, val: T) -> &'r T {
        unsafe { transmute::<&mut T, &'r T>(self.arena.alloc(val)) }
    }

    pub fn intern_ty(&self, kind: TyKind<'tcx>) -> Ty<'tcx> {
        Ty(self.types.intern(kind, |kind| {
            self.alloc(kind)
        }))
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct FieldIdx(pub u32);

impl index_vec::Idx for FieldIdx {
    fn index(self) -> usize {
        return self.0 as usize
    }

    fn from_usize(idx: usize) -> Self {
        Self(idx as u32)
    }
}

#[derive(Debug, Hash)]
pub struct AdtDefInner {
    pub def: DefId,
    pub name: Symbol,
    fields: index_vec::IndexVec<FieldIdx, FieldDef>,
    pub kind: AdtKind,
}

impl AdtDefInner {
    pub fn new(
        def: DefId,
        name: Symbol,
        fields: index_vec::IndexVec<FieldIdx, FieldDef>,
        kind: AdtKind
    ) -> Self {
        Self {
            def, name, fields, kind
        }
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

#[derive(Debug, Hash, Clone, Copy)]
pub struct AdtDef<'tcx>(&'tcx AdtDefInner);

impl<'tcx> Deref for AdtDef<'tcx> {
    type Target = AdtDefInner;

    fn deref(&self) -> &Self::Target {
        self.0
    }
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

#[derive(Debug, Hash)]
pub struct Scalar {
    size: u8,
    data: u128
}

#[derive(Debug, Hash)]
pub enum ValTree<'tcx> {
    Scalar(Scalar),
    Branch(&'tcx ValTree<'tcx>)
}

#[derive(Debug, Hash)]
pub enum ConstInner<'tcx> {
    String(&'tcx str),
    Value(Ty<'tcx>, ValTree<'tcx>),
    Placeholder
}

#[derive(Debug, Hash, Clone, Copy)]
pub struct Const<'tcx>(&'tcx ConstInner<'tcx>);

impl<'tcx> Const<'tcx> {

    pub fn try_as_usize(&self) -> Option<usize> {
        match self.0 {
            ConstInner::String(..) => None,
            ConstInner::Placeholder => None,
            ConstInner::Value(ty, val) => {
                let Ty(TyKind::Primitive(Primitive::NUint)) = ty else {
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

#[derive(Debug, Hash)]
pub enum TyKind<'tcx> {
    Primitive(Primitive),
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
            TyKind::Primitive(p) => write!(f, "{p}"),
            TyKind::Adt(adt) => f.write_str(adt.name.get()),
            TyKind::Refrence(ty) => write!(f, "*{ty}"),
            TyKind::Slice(ty) => write!(f, "[]{ty}"),
            TyKind::Array(ty, _) => write!(f, "[?]{ty}"),
            TyKind::DynamicArray(ty) => write!(f, "[..]{ty}"),
            TyKind::Function(_) => write!(f, "function"),
            TyKind::Range(ty, _) => write!(f, "Range<{ty}>"),
            TyKind::Tuple(tys) => {
                f.write_str("(")?;
                for (idx, ty) in tys.iter().enumerate() {
                    write!(f, "{ty}");
                    if idx != tys.len() - 1 {        
                        f.write_str(", ")?;
                    }
                }
                f.write_str(")")?;
                Ok(())
            }
            TyKind::Err => write!(f, "Err"),
        }
    }
}

impl<'tcx> Ty<'tcx> {
    pub fn new_array(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, cnst: Const<'tcx>) -> Ty<'tcx> {
        tcx.interners.intern_ty(TyKind::Array(ty, cnst))
    }

    pub fn new_slice(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Ty<'tcx> {
        tcx.interners.intern_ty(TyKind::Slice(ty))
    }

    pub fn new_dyn_array(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Ty<'tcx> {
        tcx.interners.intern_ty(TyKind::DynamicArray(ty))
    }

    pub fn new_refrence(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Ty<'tcx> {
        tcx.interners.intern_ty(TyKind::Refrence(ty))
    }

    pub fn new_error(tcx: TyCtxt<'tcx>) -> Ty<'tcx> {
        tcx.interners.intern_ty(TyKind::Err)
    }

    pub fn new_never(tcx: TyCtxt<'tcx>) -> Ty<'tcx> {
        tcx.interners.intern_ty(TyKind::Never)
    }

    pub fn new_primitive(tcx: TyCtxt<'tcx>, primitive: Primitive) -> Ty<'tcx> {
        tcx.interners.intern_ty(TyKind::Primitive(primitive))
    }

    pub fn new_adt(tcx: TyCtxt<'tcx>, adt: AdtDef<'tcx>) -> Ty<'tcx> {
        tcx.interners.intern_ty(TyKind::Adt(adt))
    }

    pub fn new_function(tcx: TyCtxt<'tcx>, def: DefId) -> Ty<'tcx> {
        tcx.interners.intern_ty(TyKind::Function(def))
    }

    pub fn new_range(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, inclusive: bool) -> Ty<'tcx> {
        tcx.interners.intern_ty(TyKind::Range(ty, inclusive))
    }

    pub fn new_tuple(tcx: TyCtxt<'tcx>, tys: Vec<Ty<'tcx>>) -> Ty<'tcx> {
        tcx.interners.intern_ty(TyKind::Tuple(tys))
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

    pub fn is_incomplete(&self) -> bool {
        match self {
            Ty(TyKind::Array(_, Const(ConstInner::Placeholder))) => true,
            _ => false
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Size {
    Computable(usize),
    Infinite
}

impl std::fmt::Display for Size {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Size::Computable(size) => write!(f, "{size} bytes"),
            Size::Infinite => f.write_str("layout cycle dected in computation"),
        }
    }
}

struct LayoutCtxt<'tcx> {
    tcx: TyCtxt<'tcx>,
    history: Vec<Ty<'tcx>>,
}

impl<'tcx> LayoutCtxt<'tcx> {
    const PTR_SIZE: usize = 8;

    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            history: Vec::new()
        }
    }

    fn calc_size_array(&mut self, base: Ty<'tcx>, cap: Const<'tcx>) -> Size {
        match self.size_of(base) {
            Size::Infinite => Size::Infinite,
            Size::Computable(size) =>
                Size::Computable(size * cap.try_as_usize().unwrap_or(0))
        }
    }

    fn calc_size_adt(&mut self, def: AdtDef<'tcx>) -> Size {
        match def.kind {
            AdtKind::Enum => Size::Computable(Self::PTR_SIZE), // enums have PTR_SIZE for now
            AdtKind::Struct => {
                let mut offset = 0usize;
                for (_idx, def) in def.fields() {
                    let field_ty = self.tcx.type_of(def.def);
                    let field_size = self.size_of(field_ty);
                    let field_size = match field_size {
                        Size::Computable(size) => size,
                        Size::Infinite => return Size::Infinite
                    };
                    if offset % field_size != 0 {
                        let padding = field_size - (offset % field_size);
                        offset += padding;
                    }
                    offset += field_size;
                }
                if offset % Self::PTR_SIZE != 0 {
                    let padding = Self::PTR_SIZE - (offset % Self::PTR_SIZE);
                    offset += padding;
                }
                Size::Computable(offset)
            }
            AdtKind::Union =>
                panic!("unions are not even parsable with this parser")
        }
    }

    fn calc_size_range(&mut self, ty: Ty<'tcx>) -> Size {
        let field_size = self.size_of(ty);
        let field_size = match field_size {
            Size::Computable(size) => size,
            Size::Infinite => return Size::Infinite
        };
        let mut offset = field_size;
        if offset % field_size != 0 {
            let padding = field_size - (offset % field_size);
            offset += padding;
        }
        offset += field_size;
        if offset % Self::PTR_SIZE != 0 {
            let padding = Self::PTR_SIZE - (offset % Self::PTR_SIZE);
            offset += padding;
        }

        Size::Computable(offset)
    }

    fn calc_size_tuple(&mut self, tys: &[Ty<'tcx>]) -> Size {
        let mut offset = 0usize;
        for ty in tys {
            let field_size = self.size_of(*ty);
            let field_size = match field_size {
                Size::Computable(size) => size,
                Size::Infinite => return Size::Infinite
            };
            if offset % field_size != 0 {
                let padding = field_size - (offset % field_size);
                offset += padding;
            }
            offset += field_size;
        }
        if offset % Self::PTR_SIZE != 0 {
            let padding = Self::PTR_SIZE - (offset % Self::PTR_SIZE);
            offset += padding;
        }
        Size::Computable(offset)
    }

    fn calc_size(&mut self, ty: Ty<'tcx>) -> Size {
        match ty.0 {
            TyKind::Adt(def) =>
                self.calc_size_adt(*def),
            TyKind::Tuple(tys) =>
                self.calc_size_tuple(tys),
            TyKind::Array(base, cap) =>
                self.calc_size_array(*base, *cap),
            TyKind::Range(ty, _) =>
                self.calc_size_range(*ty),
            TyKind::Refrence(..) => Size::Computable(Self::PTR_SIZE), 
            TyKind::DynamicArray(..) => Size::Computable(Self::PTR_SIZE * 3),
            TyKind::Slice(..) => Size::Computable(Self::PTR_SIZE * 2),
            TyKind::Function(..) | TyKind::Err | TyKind::Never => Size::Computable(0),
            TyKind::Primitive(prim) => Size::Computable(prim.size() as usize / 8),
        }
    }

    fn size_of(&mut self, ty: Ty<'tcx>) -> Size {
        if self.history.contains(&ty) {
            // Ty is recursive
            return Size::Infinite;
        }
        self.history.push(ty);
        let size = self.calc_size(ty);
        self.history.pop();
        size
    }
}

pub fn size_of<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Size {
    let mut ctxt = LayoutCtxt::new(tcx);
    let size = ctxt.size_of(ty);
    size
}

pub fn representable<'tcx>(tcx: TyCtxt<'tcx>, id: DefId) -> bool {
    let ty = tcx.type_of(id);
    matches!(tcx.size_of(ty), Size::Computable(..))
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum NumberSign {
    Positive, Negative
}

#[repr(u32)]
#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq)]
pub enum Primitive {
    Bool, Void,
    SByte, Byte, Short, UShort, Int, Uint, Long, ULong, Nint, NUint,
    Char, String
}

impl TryFrom<Symbol> for Primitive {
    type Error = ();

    fn try_from(value: Symbol) -> Result<Self, Self::Error> {
        if !value.is_primtive() {
            return Err(());
        }
        Ok(unsafe { transmute(value) })
    }
}

impl From<Primitive> for Symbol {
    fn from(value: Primitive) -> Self {
        unsafe { transmute(value) }
    }
}

impl std::fmt::Display for Primitive {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let symbol: Symbol = (*self).into();
        f.write_str(symbol.get())
    }
}

impl Primitive {
    pub fn integer_fit(&self, int: u64, sign: NumberSign) -> bool {
        use Primitive::*;
        if sign == NumberSign::Negative && matches!(self, Byte | UShort | Uint | ULong | NUint) {
            return false;
        }

        let signed = match self.signed() {
            Some(signed) => signed,
            None => return false,
        };
        let bits = self.size() as u32;

        let range = if sign == NumberSign::Negative { // create lower range
            1 << (bits - 1)
        } else if signed { // create "small" upper range
            (1 << (bits - 1)) - 1
        } else { // create "big" upper range
            (1u64).checked_shl(bits).unwrap_or(0).wrapping_sub(1)
        };

        int <= range
    }

    pub fn signed(&self) -> Option<bool> {
        use Primitive::*;
        Some(match self {
            SByte | Short | Int | Long | Nint => true,
            Byte | UShort | Uint | ULong | NUint  => false,
            _ => return None
        })
    }

    pub fn size(&self) -> u8 {
        use Primitive::*;
        // TODO: Decide based on platform
        // (currently only valid for 64bit platforms)
        match self {
            SByte | Byte => 8,
            Short | UShort => 16,
            Int | Uint => 32,
            Long | ULong => 64,
            Nint | NUint => 64, 
            Bool => 8, Void => 0,
            Char => 32, String => 128
        }
    }
}

