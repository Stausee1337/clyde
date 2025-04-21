use std::{cell::{Cell, RefCell}, marker::PhantomData, ops::Deref, collections::{HashMap, hash_map::Entry as StdEntry}};

use crate::{ast::{self, DefId, NodeId}, diagnostics::DiagnosticsCtxt, interface::Session, intermediate, resolve::ResolutionResults, typecheck, types};

pub struct GlobalCtxt<'tcx> {
    pub resolutions: ResolutionResults<'tcx>,
    pub arena: bumpalo::Bump,
    pub session: &'tcx Session,
    pub interners: Interners<'tcx>,
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
            interners: Interners::default(),
            providers,
            caches: QueryCaches::default(),
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
}

macro_rules! define_queries {
    ($(fn $name:ident($key:ident: $pat:ty) -> $rty:ty;)*) => {
        macro_rules! for_every_query {
            ( $callback:ident! ) => {
                $callback!($($name, $key, $pat, $rty)*);
            }
        }
    }
}

define_queries! {
    fn type_of(key: ast::DefId) -> types::Ty<'tcx>;
    fn typecheck(key: ast::DefId) -> &'tcx typecheck::TypecheckResults<'tcx>;
    fn fn_sig(key: ast::DefId) -> types::Signature<'tcx>;
    fn build_ir(key: ast::DefId) -> &'tcx intermediate::Body<'tcx>;
}

macro_rules! define_query_caches {
    ($($name:ident, $key:ident, $pat:ty, $rty:ty)*) => {
        pub struct QueryCaches<'tcx> {
            $(pub $name: RefCell<HashMap<$pat, $rty>>,)*
        }

        impl<'tcx> Default for QueryCaches<'tcx> {
            fn default() -> Self {
                Self {
                    $($name: RefCell::new(HashMap::<$pat, $rty>::default()),)*
                }
            }
        }
    }
}

macro_rules! define_providers {
    ($($name:ident, $key:ident, $pat:ty, $rty:ty)*) => { 
        pub struct Providers {
            $(pub $name: for<'tcx> fn(tcx: TyCtxt<'tcx>, $key: $pat) -> $rty,)*
        }
    }
}

macro_rules! define_tcx_impls {
    ($($name:ident, $key:ident, $pat:ty, $rty:ty)*) => {$(
        impl<'tcx> TyCtxt<'tcx> {
            pub fn $name(&self, $key: $pat) -> $rty {
                let mut cache = self.caches.$name.borrow_mut();
                match cache.entry($key) {
                    StdEntry::Occupied(entry) => *entry.get(),
                    StdEntry::Vacant(entry) => {
                        let value = (self.providers.$name)(*self, $key);
                        entry.insert(value);
                        value
                    }
                }
            }
        })*
    };
}

for_every_query! { define_query_caches! }
for_every_query! { define_providers! }
for_every_query! { define_tcx_impls! }

macro_rules! define_internables {
    ($(into $pool:ident intern $name:ident ($in:ty) -> $out:ty;)*) => {
        macro_rules! for_every_internable {
            ( $callback:ident! ) => {
                $callback!($($in, $out, $name, $pool)*);
            }
        }
    }
}

define_internables! {
    into adt_defs intern intern_adt(types::AdtDefInner) -> types::AdtDef<'tcx>;
    into tys      intern intern_ty(types::TyKind<'tcx>) -> types::Ty<'tcx>;
    into consts   intern intern_const(types::ConstInner<'tcx>) -> types::Const<'tcx>;
}

macro_rules! define_interners {
    ($($in:ty, $out:ty, $fn:ident, $pool:ident)*) => {
        pub struct Interners<'tcx> {
            phantom: std::marker::PhantomData<&'tcx ()>,
            $($pool: (),)*
        }

        impl<'tcx> Default for Interners<'tcx> {
            fn default() -> Self {
                Self {
                    phantom: PhantomData,
                    $($pool: Default::default(),)*
                }
            }
        }
    };
}

macro_rules! define_intern_fns {
    ($($in:ty, $out:ty, $fn:ident, $pool:ident)*) => {$(
        impl<'tcx> TyCtxt<'tcx> {
            pub fn $fn(&self, _input: $in) -> $out {
                let _interner = &self.interners.$pool;
                todo!();
            }
        })*
    };
}

for_every_internable! { define_interners! }
for_every_internable! { define_intern_fns! }

/*

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
*/
