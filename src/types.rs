use std::mem::transmute;

use bumpalo::Bump;
use bitflags::bitflags;

use crate::{ast::DefId, symbol::Symbol, context::{SharedHashMap, TyCtxt, Interner}, diagnostics::DiagnosticsData};

bitflags! {
    #[derive(Hash)]
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
    adt_defs: mk_adt_from_data(AdtDefInner) -> AdtDef;
}

#[derive(Default)]
pub struct CtxtInterners<'tcx> {
    arena: Bump,
    types: SharedHashMap<&'tcx TyKind<'tcx>>,
    adt_defs: SharedHashMap<&'tcx AdtDefInner>,
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

#[derive(Hash)]
pub struct AdtDefInner {
    pub def: DefId,
    pub name: Symbol,
    fields: index_vec::IndexVec<FieldIdx, FieldDef>,
    flags: AdtFlags,
}

#[derive(Hash)]
pub struct FieldDef {
    pub def: DefId,
    pub symbol: Symbol
}

#[derive(Hash, Clone, Copy)]
pub struct AdtDef<'tcx>(&'tcx AdtDefInner);

#[derive(Hash)]
pub enum TyKind<'tcx> {
    Primitive(Primitive),
    Adt(AdtDef<'tcx>)
}

#[derive(Clone, Copy)]
pub struct Ty<'tcx>(&'tcx TyKind<'tcx>);

#[repr(u32)]
#[derive(Hash)]
pub enum Primitive {
    Bool, Void,
    SByte, Byte, Short, UShort, Int, Uint, Long, ULong, Nint, NUint,
    Char, String
}

