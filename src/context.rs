use std::{borrow::Borrow, cell::{Cell, RefCell}, hash::{Hash, Hasher, BuildHasher}, ops::Deref};

use foldhash::quality::FixedState;
use hashbrown::hash_table::{HashTable, Entry as TableEntry, VacantEntry, OccupiedEntry};

use crate::{analysis::{intermediate, resolve::{self, ResolutionResults}, typecheck}, diagnostics::DiagnosticsCtxt, session::Session, syntax::{ast::{self, DefId, NodeId}, symbol::Symbol}, target, type_ir};

pub struct GlobalCtxt<'tcx> {
    pub resolutions: ResolutionResults<'tcx>,
    pub arena: bumpalo::Bump,
    pub session: &'tcx Session,
    pub interners: Interners<'tcx>,
    pub providers: Providers,
    pub caches: QueryCaches<'tcx>,
    pub basic_types: type_ir::BasicTypes<'tcx>
}

impl<'tcx> GlobalCtxt<'tcx> {
    pub fn new(
        session: &'tcx Session,
        arena: &'tcx bumpalo::Bump,
        providers: Providers,
        resolutions: ResolutionResults<'tcx>,
    ) -> GlobalCtxt<'tcx> {
        let interners = Interners::new(&arena);
        let basic_types = type_ir::BasicTypes::alloc(&interners);
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
    pub fn owner_node(self, node_id: NodeId) -> ast::Node<'tcx> {
        let global_owners = self.resolutions.ast_info.global_owners.borrow();
        let owner = &global_owners[node_id.owner];
        owner.node
    }

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

    pub fn parent_of(self, node: NodeId) -> ast::NodeId {
        let map = self.parent_map(node.owner);
        map.nodes[node.local].expect("tcx.parent_of(..) executed on dead node")
    }

    // TODO: change to associated items and more complicated generic-solving query
    // FIXME: associated items will be able to appear on any items also e.g. `int` as functions can
    // be assoicated to any sort of path e.g.: `int int::max() { return ...; }`. Querying inner
    // items by def_id is probably to narrow
    pub fn inner_items(self, id: DefId) -> &'tcx [(DefId, ast::DefinitionKind)] {
        let node = self.node_by_def_id(id);
        let ast::Node::Item(ast::Item { kind: ast::ItemKind::Struct(..), .. }) = node else {
            panic!("node {node:?} cannot not have inner items");
        };

        self.resolutions.inner_items.get(&id).map_or(&[], |vec| &vec)
    }

    pub fn module_info(self, module: &'tcx ast::SourceFile<'tcx>) -> ModuleInfo {
        let path = &self.resolutions.node_to_path_map[&module.node_id];
        let file_name = path.file_name().unwrap();
        let source_file_name = std::str::from_utf8(file_name.as_encoded_bytes()).unwrap();

        let mangled_name = todo!();

        ModuleInfo { 
            mangled_name,
            source_file_name: source_file_name.to_string()
        }
    }
}

impl<'tcx> target::DataLayoutExt for TyCtxt<'tcx> {
    fn data_layout(&self) -> &target::TargetDataLayout {
        self.session.target.data_layout()
    }
}

pub struct ModuleInfo {
    pub mangled_name: Symbol,
    pub source_file_name: String
}

macro_rules! define_queries {
    ($($(#[$outer:tt])* fn $name:ident($key:ident: $pat:ty) -> $rty:ty;)*) => {
        macro_rules! for_every_query {
            ( $callback:ident! ) => {
                $callback!($([$($outer)*], $name, $key, $pat, $rty)*);
            }
        }
    }
}

define_queries! {
    #[handle_cycle_error]
    fn type_of(id: ast::DefId) -> type_ir::Ty<'tcx>;
    fn typecheck(id: ast::DefId) -> &'tcx typecheck::TypecheckResults<'tcx>;
    fn fn_sig(id: ast::DefId) -> type_ir::Signature<'tcx>;
    fn build_ir(id: ast::DefId) -> Result<&'tcx intermediate::Body<'tcx>, ()>;
    fn enum_variant(id: ast::DefId) -> (type_ir::Ty<'tcx>, &'tcx type_ir::VariantDef<'tcx>);
    fn parent_map(owner: ast::OwnerId) -> &'tcx resolve::ParentMap;
    #[handle_cycle_error]
    fn layout_of(ty: type_ir::Ty<'tcx>) -> Result<type_ir::TyLayoutTuple<'tcx>, type_ir::LayoutError>;
    fn instantiate_body(key: (&'tcx intermediate::Body<'tcx>, &'tcx [type_ir::GenericArg<'tcx>])) -> &'tcx intermediate::Body<'tcx>;
}

macro_rules! define_query_caches {
    ($([$($outer:meta)*], $name:ident, $key:ident, $pat:ty, $rty:ty)*) => {
        pub struct QueryCaches<'tcx> {
            $($name: RefCell<Storage<$pat, $rty>>,)*
        }

        impl<'tcx> Default for QueryCaches<'tcx> {
            fn default() -> Self {
                Self {
                    $($name: RefCell::new(Storage::<$pat, $rty>::default()),)*
                }
            }
        }
    }
}

macro_rules! define_providers {
    ($([$($outer:meta)*], $name:ident, $key:ident, $pat:ty, $rty:ty)*) => { 
        pub struct Providers {
            $(pub $name: for<'tcx> fn(tcx: TyCtxt<'tcx>, $key: $pat) -> $rty,)*
        }
    }
}

macro_rules! define_tcx_impls {
    ($([$($outer:meta)*], $name:ident, $key:ident, $pat:ty, $rty:ty)*) => {$(
        impl<'tcx> TyCtxt<'tcx> {
            pub fn $name(&self, $key: $pat) -> $rty {
                use queries::{Queries, Impl};
                query_by_key::<Impl<{ Queries::$name as u32 }>>(
                    *self,
                    $key,
                    self.providers.$name,
                    &self.caches.$name,
                )
            }
        })*
    };
}

macro_rules! macro_if {
    ([$($outer:tt)*] { $($then:tt)* } { $($else:tt)* }) => {
        macro_if!(@munch [$($outer)*] { $($then)* } { $($else)* });
    };

    (@munch [handle_cycle_error $($outer:tt)*] { $($then:tt)* } { $($else:tt)* }) => {
        $($then)*
    };
    (@munch [$_:tt $($outer:tt)*] { $($then:tt)* } { $($else:tt)* }) => {
        macro_if!(@munch [$($outer)*] { $($then)* } { $($else)* }); 
    };
    (@munch [] { $($then:tt)* } { $($else:tt)* }) => {
        $($else)* 
    };
}

macro_rules! define_oop {
    ($([$($outer:tt)*], $name:ident, $key:ident, $pat:ty, $rty:ty)*) => {
        #[doc(hidden)]
        mod queries {
            use super::*;

            #[allow(non_camel_case_types)]
            #[repr(u32)]
            pub(super) enum Queries {
                $($name),*
            }

            pub(super) struct Impl<const KEY: u32>;

            $(
                impl Query for Impl<{ Queries::$name as u32 }> {
                    const NAME: &'static str = stringify!($name);

                    type Key<'tcx> = $pat;
                    type Value<'tcx> = $rty;

                    fn from_cycle_error<'tcx>(_tcx: TyCtxt<'tcx>) -> Self::Value<'tcx> {
                        macro_if! {
                            [$($outer)*] {
                                return <Self::Value<'tcx> as FromCycleError<'tcx>>::from_cycle_error(_tcx);
                            } {
                                // TODO: give better error message as the compiler is crashing
                                panic!("query `{}` went into a cycle", Self::NAME);
                            }
                        }
                    }
                }
            )*
        }
    };
}

for_every_query! { define_query_caches! }
for_every_query! { define_providers! }
for_every_query! { define_tcx_impls! }
for_every_query! { define_oop! }

pub trait FromCycleError<'tcx> {
    fn from_cycle_error(tcx: TyCtxt<'tcx>) -> Self;
}

pub trait Query {
    const NAME: &'static str;

    type Key<'a>: Hash + Eq + Copy;
    type Value<'a>: Copy;

    fn from_cycle_error<'tcx>(tcx: TyCtxt<'tcx>) -> Self::Value<'tcx>;
}

fn query_by_key<'tcx, Q: Query>(
    tcx: TyCtxt<'tcx>,
    key: Q::Key<'tcx>,
    execute: fn(TyCtxt<'tcx>, Q::Key<'tcx>) -> Q::Value<'tcx>,
    cache: &RefCell<Storage<Q::Key<'tcx>, Q::Value<'tcx>>>
) -> Q::Value<'tcx> {
    let mut lock = cache.borrow_mut();

    match lock.entry(&key) {
        StorageEntry::Vacant { entry } => {
            entry.started(key);
            drop(lock);

            execute_query::<Q>(tcx, key, execute, cache)
        }
        StorageEntry::Started { .. } => Q::from_cycle_error(tcx),
        StorageEntry::Occupied { entry } => entry
    }
}

fn execute_query<'tcx, Q: Query>(
    tcx: TyCtxt<'tcx>,
    key: Q::Key<'tcx>,
    execute: fn(TyCtxt<'tcx>, Q::Key<'tcx>) -> Q::Value<'tcx>,
    cache: &RefCell<Storage<Q::Key<'tcx>, Q::Value<'tcx>>>
) -> Q::Value<'tcx> {
    let value = execute(tcx, key);

    let mut lock = cache.borrow_mut();
    match lock.entry(&key) {
        StorageEntry::Started { mut entry } => entry.complete(value),
        _ => unreachable!("query {} expected in Started state", Q::NAME)
    }

    value
}

struct Storage<K, V> {
    table: HashTable<(K, Option<V>)>
}

impl<K, V> Default for Storage<K, V> {
    fn default() -> Self {
        Self {
            table: HashTable::new()
        }
    }
}

impl<K: Hash + Eq, V: Copy> Storage<K, V> {
    fn entry(&mut self, key: &K) -> StorageEntry<'_, K, V> {
        let hash = make_hash(key);
        match self.table.entry(hash, |(k, _)| k == key, |(k, _)| make_hash(k)) {
            TableEntry::Vacant(entry) => StorageEntry::Vacant { entry },
            TableEntry::Occupied(entry) => {
                match entry.get() {
                    (_, None) => StorageEntry::Started { entry },
                    (_, Some(v)) => StorageEntry::Occupied { entry: *v }
                }
            }
        }
    }
}

enum StorageEntry<'a, K, V> {
    Vacant {
        entry: VacantEntry<'a, (K, Option<V>)>
    },
    Started {
        entry: OccupiedEntry<'a, (K, Option<V>)>
    },
    Occupied {
        entry: V
    }
}

trait StorageStartedExt<K> {
    fn started(self, key: K);
}

trait StorageCompleteExt<V> {
    fn complete(&mut self, value: V);
}

impl<'a, K, V> StorageStartedExt<K> for VacantEntry<'a, (K, Option<V>)> {
    fn started(self, key: K) {
        self.insert((key, None));
    }
}

impl<'a, K, V> StorageCompleteExt<V> for OccupiedEntry<'a, (K, Option<V>)> {
    fn complete(&mut self, value: V) {
        self.get_mut().1 = Some(value);
    }
}

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
    into adt_defs intern intern_adt(type_ir::AdtKind) -> type_ir::AdtDef<'tcx>;
    into tys      intern intern_ty(type_ir::TyKind<'tcx>) -> type_ir::Ty<'tcx>;
    into consts   intern intern_const(type_ir::ConstKind<'tcx>) -> type_ir::Const<'tcx>;
    into layouts  intern intern_layout(type_ir::LayoutData) -> type_ir::Layout<'tcx>;
    into globals  intern intern_global(type_ir::GlobalKind<'tcx>) -> type_ir::Global<'tcx>;
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

macro_rules! define_internable {
    ($($in:ty, $($out:ident)::+, $fn:ident, $pool:ident)*) => {$(
        impl<'tcx> Internable for &'tcx $in {
            fn to_pointer(self) -> *const () {
                self as *const _ as *const ()
            }
        }
    )*}
}

macro_rules! define_lift {
    ($($in:ty, $($out:ident)::+, $fn:ident, $pool:ident)*) => {$(
        impl<'a> $($out)::+ <'a> {
            #[allow(dead_code)]
            pub fn lift<'tcx>(self, tcx: TyCtxt<'tcx>) -> Option<$($out)::+ <'tcx>> {
                tcx.interners.$pool
                    .contains(self.0)
                    .then(|| unsafe { std::mem::transmute(self) })
            }
        }
    )*}
}

for_every_internable! { define_interners! }
for_every_internable! { define_intern_fns! }
for_every_internable! { define_internable! }
for_every_internable! { define_lift! }

#[doc(hidden)]
pub trait Internable {
    fn to_pointer(self) -> *const ();
}

pub trait InternerExt<T: Hash + Copy> {
    fn intern<V: Hash + Eq>(&self, value: V, f: impl FnOnce(V) -> T) -> T 
    where
        T: Borrow<V>;

    fn contains<U: Hash + Internable>(&self, value: U) -> bool
    where
        T: Internable;
}

impl<T: Hash + Copy> InternerExt<T> for RefCell<HashTable<T>> {
    fn intern<V: Hash + Eq>(&self, value: V, f: impl FnOnce(V) -> T) -> T 
    where
        T: Borrow<V>
    {
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

    fn contains<U: Hash + Internable>(&self, value: U) -> bool
    where
        T: Internable,
    {
        let hash = make_hash(&value);
        let table = self.borrow();
        let pointer = value.to_pointer();

        table.find(hash, |item| item.to_pointer() == pointer).is_some()
    }
}

const HASH_STATE: FixedState = FixedState::with_seed(0x082efa98ec4e6c89);

fn make_hash<H: Hash>(hashable: &H) -> u64 {
    let mut hasher = HASH_STATE.build_hasher();
    hashable.hash(&mut hasher);
    hasher.finish()
}

