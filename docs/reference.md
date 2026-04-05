# The Clyde Language Reference

## Core Principles
Clyde aims to be between C++ and Rust. More precisely, it aims for the
modernedy of rust, but the more of the freedom of C++. A lot of todays hobbyist
languages, which clyde is definitely one of, seek to be a "spiritual successor"
to C: looking at the C programing language and the features it lacks, and 
deciding to transform that into a modern package. Clyde is decidably NOT that.
It seeks to be way more complex then C, or any of its modern day "successors",
with features such as: RAII, Call Stack Unwinding, Pattern Matching, and many
more.

Planned features include:
 - powerful compile time metaprograming
 - RAII (or automatic destructors)
 - generics/templating system
 - tagged unions
 - traits
 - customizable dynamic dispatch
 - operator overloading
 - methods (or instance functions using UFCS)

Clyde will NOT have:
 - inheritance (like rust)
 - borrow checker
 - garbage collector

## Syntax Overview

### File

Every `File` consists of a sequence of `Item`s.

Pseudogrammar:
```grammar
File => Item*;
```

### Items

An `Item` always starts with a identifying `Path` and then is serparted by `::`
from the actual declaration. E.g.:
```clyde
Test :: struct { x: i32; y: u32; }
```


The items path is uniquly sperated by is declaration either by a `KEYWORD`, 
`DIRECTIVE`, or `<` directly *after* or by a contextual `IDENTIFIER`
directly *before* the `::`. E.g.:

```
CAPACITY const :: 3; // Defines a const `CAPACITY` of value `3`
WIDTH const: u16: 15; // Defines const `WIDTH` with explicit type `u16`

cstring :: #type ffi::OsString; // Aliases `ffi::OsString` to `cstring`
IntMap :: <V: type> #type HashMap<i32, V>; // Generic alias to `HashMap<int,?>`
```

Pseudogrammar:
```grammar
Item => ImplicitItem | ConstItem | ModuleImport;
LimitedItem => ImplicitItemLimited | ConstItemLimited;

ImplicitItem => FullPath ItemDeclConstrainedOrNot Generics? ImplicitItemDecl;
ImplicitItemLimited => Ident
    ItemDeclConstrainedOrNot Generics? ImplicitItemDeclBase;
ConstItem => FullPath s"const" 
    ItemDeclConstrainedOrNot Generics? Expr;
ConstItemLimited => Ident s"const" 
    ItemDeclConstrainedOrNot Generics? Expr;

ItemDeclConstrainedOrNot => "::" | ":" Type ":";

ImplicitItemDecl => ModuleImport | FunctionDecl | ImplicitItemDeclBase;
ImplicitItemDeclBase => "#type" FullPath
                | StrucTypemExpr
                | EnumTypeExpr
                | UnionTypeExpr
                | TraitItemDecl;
```

**TODO: runtime syntatical elements (`RSE`) like `#run`, `#if` or `#scope`,
which can appear on the file level and in every struct, enum, trait, etc.**

### Structs

Structs consist of a sequence of named struct fields. E.g. like this
```clyde
Test :: struct { x: i32; y: u32; } // This code defines a `struct` named `Test`
with fields `x` and `y` of type `i32` and `u32` respectively
```

Pseudogrammar:
```grammar
StructTypeExpr => "struct" WhereClause? (";" | StructBody);
StructBody => "{" (NamedField | LimitedItem)* "}";
NamedField => "using"? Ident ":" Type ";";
```

A field prefixed with the `using` keyword exposes all the types fields into the
current structs context. The fields type needs to be a kind of product type.

### Enums

This is an example enum. I think enmus are pretty self-explanatory. E.g.:
```
Color :: enum : i8 {
    TRANSPARENT :: -1;
    BLACK; WHITE; GRAY;
    RED; GREEN; ORANGE; BLUE;
    LIGHTRED; LIGHTGREEN; YELLOW; LIGHTBLUE;
    MARGENTA; CYAN;
}
```

**TODO: describe #bitflag enum**
**TODO: explain #incomplete directive**

Pseudogrammar:
```grammar
EnumTypeExpr => "enum" EnumTypeRepr? EnumDirectives~ "{" EnumDiscrimant* "}";
EnumTypeRepr => ":" Type;
EnumDirectives => "#bitflags" | "#incomplete";
EnumDiscriminant => Ident ("::" Expr)? ";";
```

**NOTE TO SELF: `~` in the grammar means, parsed as list with unique elements**

### Unions
Unions are tagged unions by default, which means they function similar to rust
enums and serve the same purpose, though they can revert back to their plain
C functionality.

This is a typical tagged union:
```
WindowEvent :: union {
    WINDOW_OPEN;
    WINDOW_CLOSE_REQUEST;
    WINDOW_CLOSE;
    KEY_EVENT => using event: KeyEvent;
    MOUSE_EVENT => using event: MouseEvent;
    USER_EVENT => {
        kind: u32;
        data: *UserData;
    }
}
```
It has discriminants like an enum (known as its tags), some of which define
named fields, as they are seen in structs. If the tagged union is empty, or no 
tag defines fields, an error will be created, since an enum can be used. It is
the main mechanism for polymorphism next to *discrimnated unions* and *traits*.

A C-style union can be achived providing the `#flat` modifier:
```
Color :: union #flat {
    rgba: u32;
    using _: struct {
        a: u8; b: u8; g: u8; r: u8;
    };
}
```
This can either be useful for interfacing with C dependencies, or creating
exoctic types like this one.

Pseudogrammar:
```grammar
UnionTypeExpr => TaggedUnion | FlatUnion;

TaggedUnion => "union" "{" UnionTag* "}";
UnionTag => Ident (";" | UnionTagBody);
UnionTagBody => "=>" (NamedField | UnionTagBlockBody) ";";
UnionTagBlockBody => "{" NamedField* "}";

FlatUnion => "union" "#flat" StructBody;
```

### Traits
Traits, currently, are very similar to rust traits. They provide a generally
effective of specifying a protocol other types need to conform to. They are
always used with the *generics system*, and in this language (other than in
rust) they are really there to not have you write a lot of verbose and hard to
read `#where` queries.

```
Formatable :: trait {
    format :: (self: *Self, fmt: *var Formatter) void!FormatError;
}
```
This is a very common trait. Every type `T` is regarded as `Formatable` as soon 
as it has a method `format` with a signature corresponding to the one shown in
trait. For every such type `T` the compile-time method
`Formattable::is_statisfied(T)` returns `true`

The `#explicit` direcitve requires the implentor type `T` to do
`#run implements_for(T, Trait)` in order to impement the trait `Trait`.

Pseudogrammar:
```grammar
TraitItemDecl => "trait" "#explicit"? "{" IncompleteItem* "}";

IncompleteItem => IncompleteImplicitItem
            | IncompleteConstItem
            | LimitedItem
            | IncompleteFunctionDecl;

IncompleteItemConstraint => ":" Type;

IncompleteImplicitItem => Ident IncompleteItemConstraint;
IncompleteConstItem => Ident s"const" IncomplteItemConstraint;

IncompleteFunctionDecl => FunctionSignature ";";
```

