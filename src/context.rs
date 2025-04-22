use std::{borrow::Borrow, cell::{Cell, RefCell}, hash::{Hash, Hasher, BuildHasher}, ops::Deref};

use foldhash::quality::FixedState;
use hashbrown::{hash_map::{HashMap, Entry as MapEntry}, hash_table::{HashTable, Entry as TableEntry}};

use crate::{ast::{self, DefId, NodeId}, diagnostics::DiagnosticsCtxt, interface::Session, intermediate, resolve::ResolutionResults, typecheck, types};

pub struct GlobalCtxt<'tcx> {
    pub resolutions: ResolutionResults<'tcx>,
    pub arena: bumpalo::Bump,
    pub session: &'tcx Session,
    pub interners: Interners<'tcx>,
    pub providers: Providers,
    pub caches: QueryCaches<'tcx>,
    pub basic_types: types::BasicTypes<'tcx>
}

impl<'tcx> GlobalCtxt<'tcx> {
    pub fn new(
        session: &'tcx Session,
        arena: &'tcx bumpalo::Bump,
        providers: Providers,
        resolutions: ResolutionResults<'tcx>,
    ) -> GlobalCtxt<'tcx> {
        let interners = Interners::new(&arena);
        let basic_types = types::BasicTypes::alloc(&interners);
        Self {
            resolutions,
            arena: bumpalo::Bump::new(),
            session,
            interners,
            providers,
            caches: QueryCaches::default(),
            basic_types
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
                    MapEntry::Occupied(entry) => *entry.get(),
                    MapEntry::Vacant(entry) => {
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
    ($(into $pool:ident intern $name:ident ($in:ty) -> $($out:ident)::+ <'tcx>;)*) => {
        macro_rules! for_every_internable {
            ( $callback:ident! ) => {
                $callback!($($in, $($out)::+, $name, $pool)*);
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
    ($($in:ty, $($out:ident)::+, $fn:ident, $pool:ident)*) => {
        pub struct Interners<'tcx> {
            pub arena: &'tcx bumpalo::Bump,
            $(pub $pool: RefCell<HashTable<&'tcx $in>>,)*
        }

        impl<'tcx> Interners<'tcx> {
            fn new(arena: &'tcx bumpalo::Bump) -> Self {
                Self {
                    arena,
                    $($pool: Default::default(),)*
                }
            }
        }
    };
}

macro_rules! define_intern_fns {
    ($($in:ty, $($out:ident)::+, $fn:ident, $pool:ident)*) => {$(
        impl<'tcx> TyCtxt<'tcx> {
            pub fn $fn(&self, input: $in) -> $($out)::+ <'tcx> {
                let interner = &self.interners.$pool;
                $($out)::+ (interner.intern(input, |kind| {
                    self.interners.arena.alloc(kind)
                }))
            }
        })*
    };
}

for_every_internable! { define_interners! }
for_every_internable! { define_intern_fns! }

pub trait InternerExt<T: Borrow<V> + Hash + Copy, V: Hash + Eq> {
    fn intern(&self, value: V, f: impl FnOnce(V) -> T) -> T;
}

impl<T: Borrow<V> + Hash + Copy, V: Hash + Eq> InternerExt<T, V> for RefCell<HashTable<T>> {
    fn intern(&self, value: V, f: impl FnOnce(V) -> T) -> T {
        let hash = make_hash(&value);
        let mut table = self.borrow_mut();

        match table.entry(hash, |item| item.borrow() == &value, |item| make_hash(item)) {
            TableEntry::Occupied(entry) => *entry.get(),
            TableEntry::Vacant(entry) => {
                let v = f(value);
                entry.insert(v);
                v
            }
        }
    }
}

const HASH_STATE: FixedState = FixedState::with_seed(0x082efa98ec4e6c89);

fn make_hash<H: Hash>(hashable: &H) -> u64 {
    let mut hasher = HASH_STATE.build_hasher();
    hashable.hash(&mut hasher);
    hasher.finish()
}

