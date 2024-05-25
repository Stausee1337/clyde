use std::{cell::RefCell, collections::HashMap, hash::{Hash, Hasher}, ops::Deref};

use ahash::AHasher;

use crate::types::CtxtInterners;

pub type SharedHashMap<V> = RefCell<HashMap<u64, V>>;

pub trait Interner<V> {
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

pub struct GlobalCtxt<'tcx> {
    pub interners: CtxtInterners<'tcx>
}

impl<'tcx> GlobalCtxt<'tcx> {
    pub fn new() -> Self {
        Self { interners: CtxtInterners::default() }
    }
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

