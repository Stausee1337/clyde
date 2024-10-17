use std::{cell::RefCell, hash::{Hash, Hasher}, ops::Deref, marker::PhantomData};
use hashbrown::hash_table::{HashTable, Entry};

use ahash::AHasher;

use crate::{queries::{Providers, QueryCaches}, interface::Session, ast::{self, DefId}, diagnostics::DiagnosticsCtxt};

pub struct Interner<'tcx> {
    inner: RefCell<HashTable<(u64, *const ())>>,
    _phantom: PhantomData<&'tcx ()>
}

impl<'tcx> Interner<'tcx> {
    pub fn new() -> Self {
        Self {
            inner: RefCell::new(HashTable::default()),
            _phantom: PhantomData::default()
        }
    }

    pub fn intern<Q: Hash + Eq>(&self, q: Q, make: impl FnOnce(Q) -> &'tcx Q) -> &'tcx Q {
        let q_hash = Self::make_hash(&q);
        let mut table = self.inner.borrow_mut();

        let entry = table.entry(
            q_hash,
            |&(e_hash, e_ptr)| {
                if e_hash != q_hash {
                    return false;
                }
                // risky at only 64bits
                let e: &'tcx Q = unsafe { &*(e_ptr as *const Q) };
                q.eq(e)
            },
            |&(hash, _)| hash);

        match entry {
            Entry::Occupied(entry) => {
                let e_ptr = entry.get().1;
                let e: &'tcx Q = unsafe { &*(e_ptr as *const Q) };
                e
            }
            Entry::Vacant(entry) => {
                let e = make(q);
                let e_ptr: *const Q = &*e;
                entry.insert((q_hash, e_ptr as *const ()));
                e
            }
        }
    }

    fn make_hash<H: ?Sized + Hash>(hashable: &H) -> u64 {
        let mut hasher = AHasher::default();
        hashable.hash(&mut hasher);
        hasher.finish()
    }
}


pub struct GlobalCtxt<'tcx> {
    pub arena: bumpalo::Bump,
    pub session: &'tcx Session,
    pub interner: Interner<'tcx>,
    pub providers: Providers,
    pub caches: QueryCaches<'tcx>,
}

impl<'tcx> GlobalCtxt<'tcx> {
    pub fn new(session: &'tcx Session, providers: Providers) -> GlobalCtxt<'tcx> {
        Self {
            session,
            arena: bumpalo::Bump::new(),
            interner: Interner::new(),
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

