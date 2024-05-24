use std::{cell::RefCell, collections::HashMap, hash::{Hash, Hasher}, mem::transmute, ops::Deref};

use bumpalo::Bump;
use ahash::AHasher;

use crate::types::{TyKind, Ty, AdtDef, AdtDefInner};

macro_rules! interners {
    ($($interner:ident : $fn:ident($ty:ty) -> $ret:ident;)*) => {
        $(
            impl<'tcx> TyCtxt<'tcx> {
                pub fn $fn(&self, value: $ty) -> $ret<'tcx> {
                    $ret(self.interners.$interner.intern(value, |value| {
                        unsafe {
                            transmute::<&mut $ty, &'tcx $ty>(self.interners.arena.alloc(value))
                        }
                    }))
                }
            }
        )*
    };
}

interners! {
    adt_defs: mk_adt_from_data(AdtDefInner) -> AdtDef;
}

type SharedHashMap<V> = RefCell<HashMap<u64, V>>;

trait Interner<V> {
    fn intern<Q: Hash>(&self, v: Q, make: impl FnOnce(Q) -> V) -> V;
}

impl<V: Copy> Interner<V> for SharedHashMap<V> {
    fn intern<Q: Hash>(&self, q: Q, make: impl FnOnce(Q) -> V) -> V {
        let hash = make_hash(&q);
        let mut map = self.borrow_mut();

        match map.get(&hash) {
            Some(v) => *v,
            None => {
                let v = make(q);
                map.insert(hash, v);
                v
            }
        }        
    }
}

fn make_hash<H: Hash>(hashable: &H) -> u64 {
    let mut hasher = AHasher::default();
    hashable.hash(&mut hasher);
    hasher.finish()
}

pub struct CtxtInterners<'tcx> {
    arena: Bump,
    types: SharedHashMap<&'tcx TyKind<'tcx>>,
    adt_defs: SharedHashMap<&'tcx AdtDefInner>
}

impl<'tcx> CtxtInterners<'tcx> {
    pub fn intern_ty(&self, kind: TyKind<'tcx>) -> Ty<'tcx> {
        Ty(self.types.intern(kind, |kind| {
            unsafe {
                transmute::<&mut TyKind<'tcx>, &'tcx TyKind<'tcx>>(self.arena.alloc(kind))
            }
        }))
    }
}

pub struct GlobalCtxt<'tcx> {
    pub interners: CtxtInterners<'tcx>
}

pub struct TyCtxt<'tcx> {
    ctxt: &'tcx GlobalCtxt<'tcx>
}

impl<'tcx> Deref for TyCtxt<'tcx> {
    type Target = GlobalCtxt<'tcx>;

    fn deref(&self) -> &Self::Target {
        self.ctxt
    }
}

