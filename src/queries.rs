use crate::{ast, context::TyCtxt, types, typecheck};

macro_rules! define_queries {
    ($(fn $name:ident($pat:ty) -> $rty:ty;)*) => {
        pub mod queries {$(
            pub mod $name {
                use crate::queries::caches::*;
                use crate::*;

                pub type Storage<'tcx> = <$pat as Key>::Cache<$rty>;
            }
        )*}

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
    };
}

define_queries! {
    fn type_of(ast::DefId) -> types::Ty<'tcx>;
    fn typecheck(ast::DefId) -> &'tcx typecheck::TypecheckResults;
    fn fn_sig(ast::DefId) -> types::Signature<'tcx>;
    fn size_of(types::Ty<'tcx>) -> types::Size;
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

pub mod caches {
    use std::{fmt::Debug, hash::Hash, collections::HashMap, cell::{RefCell, OnceCell}};

    use index_vec::IndexVec;

    use crate::ast::DefId;

    pub trait QueryCache {
        type Key: Hash + Eq + Copy + Debug;
        type Value: Copy;

        fn lookup(&self, key: &Self::Key) -> Option<Self::Value>;
        fn complete(&self, key: Self::Key, value: Self::Value);
        fn iter(&self, f: &mut dyn FnMut(&Self::Key, &Self::Value));
    }

    pub struct SimpleCache<K, V> {
        cache: RefCell<HashMap<K, V, ahash::RandomState>>,
    }

    impl<K, V> Default for SimpleCache<K, V> {
        fn default() -> Self {
            Self {
                cache: RefCell::new(HashMap::default())
            }
        }
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

    pub struct OnceCache<K, V> {
        cache: RefCell<OnceCell<(K, V)>>,
    }

    impl<K: Hash + Eq + Copy + Debug, V: Copy> Default for OnceCache<K, V> {
        fn default() -> Self {
            Self { cache: RefCell::new(OnceCell::default()) }
        }
    }

    impl<K: Hash + Eq + Copy + Debug, V: Copy> QueryCache for OnceCache<K, V> {
        type Key = K;
        type Value = V;
        fn lookup(&self, key: &Self::Key) -> Option<Self::Value> {
            if let Some((skey, svalue)) = self.cache.borrow().get() {
                if key == skey {
                    return Some(*svalue);
                }
            }
            None
        }

        fn complete(&self, key: Self::Key, value: Self::Value) {
            let Err(..) = self.cache.borrow_mut().set((key, value)) else {
                return;
            };
            panic!("tried to complete a once cache multiple times");
        }

        fn iter(&self, f: &mut dyn FnMut(&Self::Key, &Self::Value)) {
           self.cache.borrow().get().map(|(k, v)| f(k, v));
        }
    }

    pub struct DefIdCache<V> {
        cache: RefCell<HashMap<DefId, V, ahash::RandomState>>
    }

    impl<V: Copy> Default for DefIdCache<V> {
        fn default() -> Self {
            Self { cache: RefCell::new(HashMap::default()) }
        }
    }

    impl<V: Copy> QueryCache for DefIdCache<V> {
        type Key = DefId;
        type Value = V;

        fn lookup(&self, key: &Self::Key) -> Option<Self::Value> {
            self.cache.borrow().get(&key).map(|value| *value)
        }
        
        fn complete(&self, key: Self::Key, value: Self::Value) { 
           self.cache.borrow_mut() 
                .insert(key, value);
        }

        fn iter(&self, _f: &mut dyn FnMut(&Self::Key, &Self::Value)) {
            todo!()
        }
    }

    pub trait Key {
        type Cache<V: Copy>: QueryCache<Value = V>;
    }

    impl Key for () {
        type Cache<V: Copy> = OnceCache<Self, V>;
    }

    impl Key for DefId {
        type Cache<V: Copy> = DefIdCache<V>;
    }

    impl<'tcx> Key for crate::types::Ty<'tcx> {
        type Cache<V: Copy> = SimpleCache<crate::types::Ty<'tcx>, V>;
    }
}
