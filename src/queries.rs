
use crate::{diagnostics, ast, parser, interface, context::TyCtxt};

macro_rules! query_if_feedable {
    ([] { $($feedable:tt)* }) => {  };
    ([feedable $($rest:tt)*] { $($feedable:tt)* }) => {
        $($feedable)* 
    };
    ([$other:tt $($modifiers:tt)*] { $($feedable:tt)* }) => {
        query_if_feedable! { [$($modifiers)*] { $($feedable)* }}
    };
}

macro_rules! define_queries {
    ($([$($modifiers:tt)*] $name:ident($pat:ty) -> $rty:ty),*) => {
        pub mod queries {$(
            pub mod $name {
                use crate::queries::caches::*;
                use crate::*;

                pub type Storage<'tcx> = <$pat as Key>::Cache<$rty>;
            }
        )*}

        $(query_if_feedable! {
            [$($modifiers:tt)*] {
            impl<'tcx> crate::context::TyCtxtFeed<'tcx, $pat> {
                pub fn $name(&self, value: $rty) {
                    use crate::queries::caches::QueryCache;

                    let key = self.key();
                    let cache = &self.tcx.caches.$name;

                    match cache.lookup(&key) {
                        Some(..) => {
                            todo!("Handle double feeding error")
                        }
                        None => {
                            cache.complete(key, value);
                        }
                    }
                }
            }
        }})*

        impl<'tcx> crate::context::TyCtxt<'tcx> {
            $(
                pub fn $name(&self, key: $pat) -> $rty {
                    execute_query(
                        *self,
                        self.providers.$name,
                        &self.caches.$name,
                        key
                    )
                }
            )*
        }

        pub struct QueryCaches<'tcx> {
            $(
                pub $name: crate::queries::queries::$name::Storage<'tcx>, 
            )*
        }

        impl<'tcx> Default for QueryCaches<'tcx> {
            fn default() -> Self {
                Self {$(
                    $name: crate::queries::queries::$name::Storage::<'tcx>::default(),
                )*}
            }
        }

        pub struct Providers {
            $(
                pub $name: for<'tcx> fn(tcx: crate::context::TyCtxt<'tcx>, key: $pat) -> $rty,
            )*
        }

        impl Providers {
            fn empty() -> Self {
                Self {
                    $(
                        $name: |_, key| query_panic(stringify!($name), &key),
                    )*
                }
            }
        }
    };
}


macro_rules! providers {
    ($(@$name:ident($provider:path)),*) => {
        impl Default for Providers {
            fn default() -> Self {
                Self {
                    $(
                        $name: $provider,
                    )*
                    ..Self::empty()
                }
            }
        }
    }
}

define_queries! {
    [feedable] file_path_and_source(interface::FileIdx) -> (&'tcx std::path::Path, &'tcx str),
    [feedable] diagnostics_for_file(interface::FileIdx) -> diagnostics::Diagnostics<'tcx>,
    [feedable] file_ast(interface::FileIdx) -> &'tcx ast::SourceFile
}

providers! {
    @diagnostics_for_file(diagnostics::create_for_file)
}

fn execute_query<'tcx, Cache: caches::QueryCache>(
    tcx: TyCtxt<'tcx>,
    execute: fn(TyCtxt<'tcx>, Cache::Key) -> Cache::Value,
    cache: &Cache,
    key: Cache::Key
) -> Cache::Value {
    match cache.lookup(&key) {
        Some(value) => value,
        None => {
            let value = execute(tcx, key);
            cache.complete(key, value);
            value
        }
    }
}

pub fn query_panic(name: &str, key: &dyn std::fmt::Debug) -> ! {
    panic!(
        "The query {name:?} has no provider function\
associated with it, for key {key:?}.
hint: Maybe the query is feedable, \
consider feeding the query first, using feed.{name}(...) on its associated feedable"
    )
}

pub mod caches {
    use std::{fmt::Debug, hash::Hash, collections::HashMap, cell::RefCell};

    use index_vec::IndexVec;

    use crate::interface::FileIdx;

    pub trait QueryCache {
        type Key: Hash + Eq + Copy + Debug;
        type Value: Copy;

        fn lookup(&self, key: &Self::Key) -> Option<Self::Value>;
        fn complete(&self, key: Self::Key, value: Self::Value);
        fn iter(&self, f: &mut dyn FnMut(&Self::Key, &Self::Value));
    }

    #[derive(Default)]
    pub struct SimpleCache<K, V> {
        cache: RefCell<HashMap<K, V, ahash::RandomState>>,
    }

    impl<K: Hash + Eq + Copy + Debug, V: Copy> QueryCache for SimpleCache<K, V> {
        type Key = K;
        type Value = V;

        fn lookup(&self, key: &Self::Key) -> Option<Self::Value> {
            let borrow = self.cache.borrow_mut();
            borrow.get(key).map(|v| *v)
        }

        fn complete(&self, key: Self::Key, value: Self::Value) {
            let mut borrow = self.cache.borrow_mut();
            borrow.insert(key, value);
        }

        fn iter(&self, f: &mut dyn FnMut(&Self::Key, &Self::Value)) {
            self.cache.borrow()
                .iter()
                .for_each(|(k, v)| f(k, v));
        }
    }

    pub struct VecCache<K: index_vec::Idx, V> {
        cache: RefCell<IndexVec<K, V>>,
    }

    impl<K: index_vec::Idx, V> VecCache<K, V> {
        pub fn end(&self) -> K {
            K::from_usize(self.cache.borrow().len())
        }
    }

    impl<K: index_vec::Idx, V> Default for VecCache<K, V> {
        fn default() -> Self {
            Self { cache: RefCell::default() }
        }
    }

    impl<K: index_vec::Idx, V: Copy> QueryCache for VecCache<K, V> {
        type Key = K;
        type Value = V;

        fn lookup(&self, key: &Self::Key) -> Option<Self::Value> {
            let borrow = self.cache.borrow();
            borrow.get(*key).map(|v| *v)
        }

        fn complete(&self, key: Self::Key, value: Self::Value) {
            let mut borrow = self.cache.borrow_mut();
            borrow.insert(key, value);
        }

        fn iter(&self, f: &mut dyn FnMut(&Self::Key, &Self::Value)) {
            self.cache.borrow()
                .iter_enumerated()
                .for_each(|(k, v)| f(&k, v));
        }
    }

    pub trait Key {
        type Cache<V: Copy>: QueryCache<Value = V>;
    }

    impl Key for FileIdx {
        type Cache<V: Copy> = VecCache<Self, V>;
    }
}
