use std::{cell::RefCell, collections::HashMap, hash::{Hash, Hasher}, ops::Deref, mem::transmute, marker::PhantomData};

use ahash::AHasher;

use crate::{types::CtxtInterners, queries::{Providers, QueryCaches}, interface::{Session, self}, ast::{self, DefId}, diagnostics::DiagnosticsCtxt};

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
    pub arena: bumpalo::Bump,
    pub session: &'tcx Session,
    pub interners: CtxtInterners<'tcx>,
    pub providers: Providers,
    pub caches: QueryCaches<'tcx>,
}

impl<'tcx> GlobalCtxt<'tcx> {
    pub fn new(session: &'tcx Session, providers: Providers) -> GlobalCtxt<'tcx> {
        Self {
            session,
            arena: bumpalo::Bump::new(),
            interners: CtxtInterners::default(),
            providers,
            caches: QueryCaches::default()
        }
    }

    pub fn enter<R, F: FnOnce(TyCtxt<'tcx>) -> R>(&'tcx self, do_work: F) -> R {
        let tcx = TyCtxt { gcx: self };
        do_work(tcx)
    }

    pub fn diagnostics(&self) -> &DiagnosticsCtxt {
        self.session.diagnostics()
    }
}

#[derive(Clone, Copy)]
pub struct TyCtxt<'tcx> {
    gcx: &'tcx GlobalCtxt<'tcx>
}

impl<'tcx> TyCtxt<'tcx> {
    pub fn node_by_def_id(self, _id: DefId) -> ast::Node<'tcx> {
        todo!()
    }
}

impl<'tcx> Deref for TyCtxt<'tcx> {
    type Target = &'tcx GlobalCtxt<'tcx>;

    fn deref(&self) -> &Self::Target {
        &self.gcx
    }
}

