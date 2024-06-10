use std::mem::transmute;

use bumpalo::Bump;
use bitflags::bitflags;

use crate::{ast::DefId, symbol::Symbol, context::{SharedHashMap, TyCtxt, Interner}, diagnostics::DiagnosticsData};

bitflags! {
    #[derive(Debug, Hash)]
    pub struct AdtFlags: u32 {
        const ENUM = 0b01;
        const STRUCT = 0b10;
        const UNION = 0b11;
    }
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
    consts: mk_const_from_inner(ConstInner) -> Const;
}

#[derive(Default)]
pub struct CtxtInterners<'tcx> {
    arena: Bump,
    types: SharedHashMap<&'tcx TyKind<'tcx>>,
    adt_defs: SharedHashMap<&'tcx AdtDefInner>,
    consts: SharedHashMap<&'tcx ConstInner>,
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
    flags: AdtFlags,
}

#[derive(Debug, Hash)]
pub struct FieldDef {
    pub def: DefId,
    pub symbol: Symbol
}

#[derive(Debug, Hash, Clone, Copy)]
pub struct AdtDef<'tcx>(&'tcx AdtDefInner);

#[derive(Debug, Hash)]
pub enum ConstInner {
    Direct,
    Infer,
    Err
}

#[derive(Debug, Hash, Clone, Copy)]
pub struct Const<'tcx>(&'tcx ConstInner);

#[derive(Debug, Hash)]
pub enum TyKind<'tcx> {
    Primitive(Primitive),
    Adt(AdtDef<'tcx>),
    Refrence(Ty<'tcx>),
    Array(Ty<'tcx>, Const<'tcx>),
    DynamicArray(Ty<'tcx>),
    Err
}

#[derive(Debug, Clone, Copy, Hash)]
pub struct Ty<'tcx>(pub &'tcx TyKind<'tcx>);

impl<'tcx> PartialEq for Ty<'tcx> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.0, other.0)
    }
}

impl<'tcx> Eq for Ty<'tcx> {

}

impl<'tcx> Ty<'tcx> {
    pub fn new_array(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, cnst: Const<'tcx>) -> Ty<'tcx> {
        tcx.interners.intern_ty(TyKind::Array(ty, cnst))
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

    pub fn new_primitive(tcx: TyCtxt<'tcx>, primitive: Primitive) -> Ty<'tcx> {
        tcx.interners.intern_ty(TyKind::Primitive(primitive))
    }

    pub fn new_adt(tcx: TyCtxt<'tcx>, adt: AdtDef<'tcx>) -> Ty<'tcx> {
        tcx.interners.intern_ty(TyKind::Adt(adt))
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum NumberSign {
    Positive, Negative
}

#[repr(u32)]
#[derive(Debug, Hash)]
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

impl Primitive {
    pub fn integer_fit(&self, int: u64, sign: NumberSign) -> bool {
        use Primitive::*;
        if sign == NumberSign::Negative && matches!(self, Byte | UShort | Uint | ULong | NUint) {
            return false;
        }
        let signed = match self {
            SByte | Short | Int | Long | Nint => true,
            Byte | UShort | Uint | ULong | NUint  => false,
            _ => return false
        };

        let bits: u64 = match self {
            SByte | Byte => 8,
            Short | UShort => 16,
            Int | Uint => 32,
            Long | ULong => 64,
            Nint | NUint => 64, // TODO: Decide based on platform
            _ => unreachable!()
        };

        let range = if sign == NumberSign::Negative { // create lower range
            1 << (bits - 1)
        } else if signed { // create "small" upper range
            (1 << (bits - 1)) - 1
        } else { // create "big" upper range
            (1 << bits) - 1
        };

        int <= range
    }
}

