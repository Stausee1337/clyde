use std::{
    mem::{ManuallyDrop, transmute},
    hash::{BuildHasherDefault, Hasher},
    cell::RefCell,
    fmt::Debug
};

use bumpalo::Bump;

type StringSet = indexmap::IndexSet<&'static str, BuildHasherDefault<GNUHasher>>;

struct StringInterner {
    arena: ManuallyDrop<Bump>,
    strings: StringSet
}

impl StringInterner {
    fn prefill(fill: &[&'static str]) -> Self {
        Self {
            arena: ManuallyDrop::new(Bump::new()),
            strings: fill.iter().copied().collect() 
        }
    }

    fn add(&mut self, str: &str) -> u32 {
        if let Some(idx) = self.strings.get_index_of(str) {
            return idx as u32;
        }

        let str = self.arena.alloc_str(str);
        let str: &'static str = unsafe { transmute(str) };

        let (idx, newly_inserted) = self.strings.insert_full(str);
        assert!(newly_inserted);

        idx as u32
    }

    fn get(&self, idx: u32) -> &str {
        self.strings.get_index(idx as usize).unwrap()
    }
}

struct GNUHasher(u32);

impl Default for GNUHasher {
    fn default() -> Self {
        GNUHasher(5381)
    }
}

impl Hasher for GNUHasher {
    fn write(&mut self, bytes: &[u8]) {
        for byte in bytes {
            self.0 = (self.0 << 5).wrapping_add(self.0).wrapping_add(*byte as u32);
        }
    }

    fn finish(&self) -> u64 {
        self.0 as u64
    }
}

const PRIMITIVES: &[&'static str] = &[
    "bool", "void",
    "sbyte", "byte", "short", "ushort", "int", "uint", "long", "ulong", "nint", "nuint",
    "char", "str"
];

thread_local! {
    static INTERNED_STRINGS: RefCell<StringInterner> = RefCell::new(StringInterner::prefill(PRIMITIVES));
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Symbol(u32);

impl Debug for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Symbol({})", self.get())
    }
}

impl Symbol {
    pub fn intern(str: &str) -> Self {
        Self(INTERNED_STRINGS.with(|interner| interner.borrow_mut().add(str)))
    }

    pub fn get(&self) -> &str {
        INTERNED_STRINGS.with(|interner| unsafe {
            transmute(interner.borrow().get(self.0))
        })
    }

    pub fn is_primtive(&self) -> bool {
        return self.0 < PRIMITIVES.len() as u32
    }
}
