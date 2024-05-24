use bitflags::bitflags;

use crate::{ast::DefId, symbol::Symbol};

bitflags! {
    #[derive(Hash)]
    pub struct AdtFlags: u32 {
        const ENUM = 0b01;
        const STRUCT = 0b10;
        const UNION = 0b11;
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

#[derive(Hash)]
pub struct AdtDef<'tcx>(pub &'tcx AdtDefInner);

#[derive(Hash)]
pub enum TyKind<'tcx> {
    Primitive(Primitive),
    Adt(AdtDef<'tcx>)
}

pub struct Ty<'tcx>(pub &'tcx TyKind<'tcx>);

#[repr(u32)]
#[derive(Hash)]
pub enum Primitive {
    Bool, Void,
    SByte, Byte, Short, UShort, Int, Uint, Long, ULong, Nint, NUint,
    Char, String
}

