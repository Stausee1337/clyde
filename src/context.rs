use std::{cell::RefCell, collections::HashMap, hash::{Hash, Hasher}, ops::Deref, mem::transmute};

use ahash::AHasher;

use crate::{types::CtxtInterners, queries::{Providers, QueryCaches}, interface::{Session, self}};

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
    arena: bumpalo::Bump,
    pub session: &'tcx Session,
    pub interners: CtxtInterners<'tcx>,
    pub providers: Providers,
    pub caches: QueryCaches<'tcx>,
}

impl<'tcx> GlobalCtxt<'tcx> {
    pub fn new(session: &'tcx Session) -> GlobalCtxt<'tcx> {
        Self {
            session,
            arena: bumpalo::Bump::new(),
            interners: CtxtInterners::default(),
            providers: Providers::default(),
            caches: QueryCaches::default()
        }
    }

    pub fn enter<R, F: FnOnce(TyCtxt<'tcx>) -> R>(&'tcx self, do_work: F) -> R {
        let tcx = TyCtxt { gcx: self };
        do_work(tcx)
    }

    pub fn alloc<T>(&self, val: T) -> &'tcx T {
        unsafe { transmute::<&mut T, &'tcx T>(self.arena.alloc(val)) }
    }

    pub fn alloc_str(&self, string: &str) -> &'tcx str {
        unsafe { transmute::<&mut str, &'tcx str>(self.arena.alloc_str(string)) }
    }
}

#[derive(Clone, Copy)]
pub struct TyCtxt<'tcx> {
    gcx: &'tcx GlobalCtxt<'tcx>
}

impl<'tcx> Deref for TyCtxt<'tcx> {
    type Target = GlobalCtxt<'tcx>;

    fn deref(&self) -> &Self::Target {
        self.gcx
    }
}

impl<'tcx> TyCtxt<'tcx> {
    pub fn create_file(self, idx: Option<interface::FileIdx>) -> TyCtxtFeed<'tcx, interface::FileIdx> {
        TyCtxtFeed { tcx: self, key: idx.unwrap() }
    }
}

#[derive(Clone, Copy)]
pub struct TyCtxtFeed<'tcx, K: Copy> {
   pub tcx: TyCtxt<'tcx>,
   key: K
}

impl<'tcx, K: Copy> TyCtxtFeed<'tcx, K> {
    #[allow(unused)]
    pub fn key(&self) -> K {
        return self.key;
    }
}
