use std::{cell::RefCell, fmt::{Debug, Display}, mem::{transmute, ManuallyDrop}};

use bumpalo::Bump;
use foldhash::quality::RandomState;

struct StringInterner {
    arena: ManuallyDrop<Bump>,
    strings: indexmap::IndexSet<&'static str, RandomState>
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

macro_rules! Symbols {
    ($($symbol:ident),*) => {
        macro_rules! for_every_sym {
            ( $callback:ident! ) => {
                $callback!($($symbol),*);
            }
        }
    }
}

Symbols! {
    bool,
    void,
    sbyte,
    byte,
    short,
    ushort,
    int,
    uint,
    long,
    ulong,
    nint,
    nuint,
    float,
    double,
    char,
    string,
    tuple,
    export,
    module,
    main,
    link_name,
    stringdata,
    stringlen,
    slice_to_raw_parts,
    string_from_raw_parts,
    T
}

macro_rules! define_symbols {
    ($($symbol:ident),*) => {
        const SYMBOLS: &[&'static str] = &[$(stringify![$symbol]),*];
    }
}

macro_rules! define_mod {
    ($($symbol:ident),*) => {
    #[allow(non_upper_case_globals)]
    #[allow(dead_code)]
    pub mod sym {
        use super::Symbol;

        #[doc(hidden)]
        #[repr(u32)]
        #[allow(non_camel_case_types)]
        enum Symbols {
            $($symbol),*
        }


        $(
            pub const $symbol: Symbol = Symbol(Symbols::$symbol as u32);
        )*
    }
    }
}

for_every_sym! { define_symbols! }
for_every_sym! { define_mod! }

thread_local! {
    static INTERNED_STRINGS: RefCell<StringInterner> = RefCell::new(StringInterner::prefill(SYMBOLS));
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Symbol(u32);

impl Debug for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Symbol({})", self.get())
    }
}

impl Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.get())
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
}
