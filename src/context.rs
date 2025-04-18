use std::{any::TypeId, cell::{Cell, RefCell}, hash::{Hash, Hasher}, marker::PhantomData, ops::Deref};
use hashbrown::hash_table::{HashTable, Entry};

use ahash::AHasher;

use crate::{ast::{self, DefId, NodeId}, diagnostics::DiagnosticsCtxt, interface::Session, intermediate, resolve::ResolutionResults, typecheck, types};

macro_rules! define_queries {
    ($(fn $name:ident($pat:ty) -> $rty:ty;)*) => {
        pub struct QueryCaches<'tcx> {
            $(
                pub $name: std::cell::RefCell<std::collections::HashMap<$pat, $rty>>, 
            )*
        }

        impl<'tcx> Default for QueryCaches<'tcx> {
            fn default() -> Self {
                Self {
                    $(
                        $name: std::cell::RefCell::new(std::collections::HashMap::<$pat, $rty>::default()),
                    )*
                }
            }
        }

        pub struct Providers {
            $(
                pub $name: for<'tcx> fn(tcx: crate::context::TyCtxt<'tcx>, key: $pat) -> $rty,
            )*
        }

        impl<'tcx> crate::context::TyCtxt<'tcx> {
            $(
                pub fn $name(&self, key: $pat) -> $rty {
                    use std::collections::hash_map::Entry;

                    let mut cache = self.caches.$name.borrow_mut();
                    match cache.entry(key) {
                        Entry::Occupied(entry) => *entry.get(),
                        Entry::Vacant(entry) => {
                            let value = (self.providers.$name)(*self, key);
                            entry.insert(value);
                            value
                        }
                    }
                }
            )*
        }
    };
}

pub struct GlobalCtxt<'tcx> {
    pub resolutions: ResolutionResults<'tcx>,
    pub arena: bumpalo::Bump,
    pub session: &'tcx Session,
    pub interner: Interner<'tcx>,
    pub providers: Providers,
    pub caches: QueryCaches<'tcx>,
}

impl<'tcx> GlobalCtxt<'tcx> {
    pub fn new(
        session: &'tcx Session,
        providers: Providers,
        resolutions: ResolutionResults<'tcx>,
    ) -> GlobalCtxt<'tcx> {
        Self {
            resolutions,
            session,
            arena: bumpalo::Bump::new(),
            interner: Interner::new(),
            providers,
            caches: QueryCaches::default()
        }
    }

    pub fn enter<R, F: FnOnce(TyCtxt<'tcx>) -> R>(&'tcx self, do_work: F) -> R {
        let tcx = TyCtxt { gcx: self };
        enter(&tcx, || do_work(tcx))
    }

    pub fn diagnostics(&self) -> &DiagnosticsCtxt {
        self.session.diagnostics()
    }
}

thread_local! {
    static TLV: Cell<*const ()> = Cell::new(std::ptr::null_mut());
}

fn enter<'tcx, F: FnOnce() -> R, R>(ctxt: &TyCtxt<'tcx>, f: F) -> R {
    TLV.with(|tlv| {
        let old = tlv.replace(ctxt as *const _ as *const ());
        let r = f();
        tlv.set(old);
        r
    })
}

unsafe fn unerase<'a, 'tcx>(ctxt: *const ()) -> &'a TyCtxt<'tcx> {
    &*(ctxt as *const TyCtxt<'tcx>)
}

pub fn with_tcx<F, R>(f: F) -> R
where
    F: for<'a, 'tcx> FnOnce(Option<&'a TyCtxt<'tcx>>) -> R
{
    TLV.with(|tlv| {
        let ctxt = tlv.get();
        let r = if ctxt.is_null() {
            f(None)
        } else {
            unsafe { f(Some(unerase(ctxt))) }
        };

        r
    })
}

#[derive(Clone, Copy)]
pub struct TyCtxt<'tcx> {
    gcx: &'tcx GlobalCtxt<'tcx>
}

impl<'tcx> Deref for TyCtxt<'tcx> {
    type Target = &'tcx GlobalCtxt<'tcx>;

    fn deref(&self) -> &Self::Target {
        &self.gcx
    }
}

impl<'tcx> TyCtxt<'tcx> {
    pub fn get_node_by_id(self, node_id: NodeId) -> ast::Node<'tcx> {
        let global_owners = self.resolutions.ast_info.global_owners.borrow();
        let owner = &global_owners[node_id.owner];
        owner.children[node_id.local]
    }

    pub fn node_by_def_id(self, id: DefId) -> ast::Node<'tcx> {
        let def = &self.resolutions.declarations[id];
        self.get_node_by_id(def.node)
    }

    pub fn def_kind(self, id: DefId) -> ast::DefinitionKind {
        let def = &self.resolutions.declarations[id];
        def.kind
    }

    #[inline]
    pub fn intern<Q: Internable<'tcx>>(self, q: Q) -> Q::Interned<'tcx> {
        q.intern(self)
    }
}

define_queries! {
    fn type_of(ast::DefId) -> types::Ty<'tcx>;
    fn typecheck(ast::DefId) -> &'tcx typecheck::TypecheckResults<'tcx>;
    fn fn_sig(ast::DefId) -> types::Signature<'tcx>;
    fn build_ir(ast::DefId) -> &'tcx intermediate::Body<'tcx>;
}

pub trait Internable<'tcx>: Hash + Eq {
    type Marker: Sized + 'static;
    type Interned<'a>: Sized;

    fn intern(self, tcx: TyCtxt<'tcx>) -> Self::Interned<'tcx>;
}

pub struct Interner<'tcx> {
    inner: RefCell<HashTable<(TypeId, u64, *const ())>>,
    _phantom: PhantomData<&'tcx ()>
}

impl<'tcx> Interner<'tcx> {
    pub fn new() -> Self {
        Self {
            inner: RefCell::new(HashTable::default()),
            _phantom: PhantomData::default()
        }
    }

    pub fn intern<Q: Internable<'tcx>>(&self, q: Q, tcx: TyCtxt<'tcx>) -> &'tcx Q {
        let q_hash = Self::make_hash(&q);
        let q_type_id = TypeId::of::<Q::Marker>();
        let mut table = self.inner.borrow_mut();

        let entry = table.entry(
            q_hash,
            |&(e_type_id, e_hash, e_ptr)| {
                if e_hash != q_hash {
                    return false;
                }
                if e_type_id != q_type_id {
                    return false;
                }
                let e: &'tcx Q = unsafe { &*(e_ptr as *const Q) };
                q.eq(e)
            },
            |&(_, hash, _)| hash);

        match entry {
            Entry::Occupied(entry) => {
                let e_ptr = entry.get().2;
                let e: &'tcx Q = unsafe { &*(e_ptr as *const Q) };
                e
            }
            Entry::Vacant(entry) => {
                let e = tcx.arena.alloc(q);
                let e_ptr: *const Q = &*e;
                entry.insert((q_type_id, q_hash, e_ptr as *const ()));
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

