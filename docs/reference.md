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
 - inheritance
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

```clyde
CAPACITY const :: 3; // Defines a const `CAPACITY` of value `3`
WIDTH const: u16: 15; // Defines const `WIDTH` with explicit type `u16`

cstring :: #type ffi::OsString; // Aliases `ffi::OsString` to `cstring`
IntMap :: <V: type> #type HashMap<i32, V>; // Generic alias to `HashMap<int,?>`
```

Pseudogrammar:
```grammar
Item => ImplicitItem | ConstItem | OperatorItem | ModuleImport;
LimitedItem => ImplicitItemLimited | ConstItemLimited;

ImplicitItem => FullPath ItemDeclConstrainedOrNot Generics? ImplicitItemDecl;
ImplicitItemLimited => Ident
    ItemDeclConstrainedOrNot Generics? ImplicitItemDeclBase;
ConstItem => FullPath s"const" 
    ItemDeclConstrainedOrNot Generics? Expr;
ConstItemLimited => Ident s"const" 
    ItemDeclConstrainedOrNot Generics? Expr;

ItemDeclConstrainedOrNot => "::" | ":" Type ":";

ImplicitItemDecl => ModuleImport 
                | FunctionDecl
                | ImplicitItemDeclBase;

ImplicitItemDeclBase => "#type" FullPath
                | StrucTypemExpr
                | EnumTypeExpr
                | UnionTypeExpr
                | TraitItemDecl;
```

**TODO: add items that start with a directive like `#run`, `#if`, `#scope`,
`#static` which can appear on the file level and in every struct, enum, trait,
etc.**

**NOTE TO SELF: `#run` (along with maybe some others) can also be used after
an item declaration. E.g.: 
`OPTIMAL_PACKING const :: #run compute_optimal_constant();`**

**NOTE TO SELF: some of these items might be called runtime syntatical elements
(`RSE`)**

### Structs

Structs consist of a sequence of named struct fields. E.g. like this
```clyde
Test :: struct { x: i32; y: u32; } // This code defines a `struct` named `Test`
// with fields `x` and `y` of type `i32` and `u32` respectively
```

Inside a structs body, inner items can be declared: like enums, unions and
other structs. Though no functions, which are always implmented on the
top-level of a file. E.g.:
```clyde
HashMap :: <K: type, V: type>struct {
    Entry :: union {
        VACANT;
        OCCUPIED => {
            key:   K;
            value: V;
        }
    }
}
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
```clyde
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
EnumTypeExpr => "enum" EnumTypeRepr? EnumDirective* "{" EnumDiscrimant* "}";
EnumTypeRepr => ":" Type;
EnumDirective => "#bitflags" | "#incomplete";
EnumDiscriminant => Ident ("::" Expr)? ";";
```

### Unions
Unions are tagged unions by default, which means they function similar to rust
enums and serve the same purpose, though they can revert back to their plain
C functionality.

This is a typical tagged union:
```clyde
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
```clyde
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
effective way of specifying a protocol other types need to conform to. They are
always used with the *generics system*, and in this language (other than in
rust) they are really there to not have you write a lot of verbose and hard to
read `#where` queries.

```clyde
Formatable :: trait {
    format :: (self: *Self, fmt: *var Formatter) void!FormatError;
}
```
This is a very common trait. Every type `T` is regarded as `Formatable` as soon
as it has a method `format` with a signature corresponding to the one shown in
trait. For every such type `T` the compile-time method 
`Formattable::is_satisfied(T)` returns `true`.

The `#explicit` direcitve requires the implentor type `T` to do
`#run implements_for(T, Trait)` in order to impement the trait `Trait`.

Theres also empty traits, which require the `is_statisfied()` method
to be implemented manually.
```clyde
Integer :: trait;
Integer::is_satisfied :: (type: *compiler::Type) bool #const {
    if type == {
        case i8 | i16 | i32 | i64 | int |
            u8 | u16 | u32 | u64 | uint => return true;
        case => return false;
    }
}
```

Pseudogrammar:
```grammar
TraitItemDecl => BodyTraitDecl | EmptyTraitDecl;
BodyTraitDecl => "trait" (":" TraitRequirements)? "#explicit"?
        "{" (IncompleteItem | IncompleteOperatorItem)* "}";
EmptyTraitDecl => "trait" ";";

IncompleteItem => IncompleteImplicitItem
            | IncompleteConstItem
            | LimitedItem
            | IncompleteFunctionDecl;

TraitRequirements => TraitRequirement ("," TraitRequirements)?;

IncompleteItemConstraint => ":" Type;

IncompleteImplicitItem => Ident IncompleteItemConstraint;
IncompleteConstItem => Ident s"const" IncomplteItemConstraint;

IncompleteFunctionDecl => Generics? FunctionSignature WhereClause? ";";

IncompleteOperatorItem => "operator" OverloadableOperator
                    "::" Generics? IncompleteOperatorDecl;
IncompleteOperatorDecl =>FunctionSignature OperatorDirective* WhereCaluse? ";";
```

### Functions
Functions are functions and they function like functions function.
```clyde
main :: () {
    println("Hello, Clyde!");
}
```

This is a classical `main` function, representing the programs entrypoint. It
declares no parameters, and has implicit return type `void`. In its body the
function `println` is called with one argument.

Function parameters are declared `name: type` and delimited by a `,`. Arguments
can be prefixed with a `using` keyword, exporting the types fields into the
functions scope. The result type is written immediately behind the closing
paren `)` with an optional error type delmited by a `!`. E.g.:
```clyde
// This function declares one parameter `s` of type `string`, returns an i32
// in the success and an `IntParseError` in the error case.
parse_int :: (s: string) i32!IntParseError {
    // ...
}
```

**TODO: explain #inline, #expand, #const**

```grammar
FunctionDecl => FunctionSignature FunctionDirective*
            WhereCaluse? (";" | Block);

FunctionSignature => "(" FunctionParameters? ")" FunctionResultSignature?;

FunctionParameters => FunctionParameter ("," FunctionParameters)?;
FunctionParameter => "using"? Ident ":" Type;

FunctionResultSignature => Type ("!" Type)?;

FunctionDirective => "#compiler"
                | "#expand"
                | "#link"
                | ExternCCallDirective
                | FunctionDirectiveBase;

FunctionDirectiveBase => "#inline" | "#const";

ExternCCallDirective => "#c_call" ExternCCallDirectiveTree?;
ExternCCallDirectiveTree => "(" s"link_name" "=" StringLit  ")";
```

### Operators
Operators can be overloaded in clyde. This can look something like this:
```clyde
Buffer :: struct {
    length: uint;
    data:   *u8;
}

// Overloading the `==` opeartor between two `Buffer`s
operator == :: (using _: *Buffer, other: *Buffer) bool {
    return length == other.length && cmp_ptr_data(data, other.data, length);
}
```

Some operators should be marked with `#symmetic` to allow for easier usage
between types. E.g.:
```clyde
Vector2 :: struct {
    x: f32;
    y: f32;
}

operator * :: (vec: Vector2, factor: f32) Vector2 #symmetric {
    return Vector2 {
        x = vec.x * factor,
        y = vec.y * factor
    };
}

vec1 := Vector2 { x = 42, y = 69 };
vec2 := vec1 * 1337; // Always works, since implemented
vec2 := 1337 * vec1; // Also works, due to `#symmetric`
```

Support for binary and unary operators is implicit via parameter count.
```
// This implements the binary `v1 - v2` subtraction operation, since the 
// operator takes two arguments
operator - :: (a: Vector2, b: Vector2) Vector2 {
    return Vector2 { x = a.x - b.x, y = a.y - b.y };
}

// This implemets the unary `-v1` negation operation, since the operator only
// takes one argument
operator - :: (using _: Vector2) Vector2 {
    return Vector2 { x = -x, y = -y };
}
```

Pseudogrammar:
```grammar
OperatorItem => "operator" OverloadableOperator "::" Generics? OperatorDecl;

OverloadableOperator => "==" | "!=" | "<" | "<=" | ">" | ">="
                    | "|" | "^" | "&"
                    | "<<" | ">>"
                    | "+" | "-" | "*" | "/" | "%"
                    | "|=" | "&=" | "^="
                    | "<<=" | ">>="
                    | "+=" | "-=" | "*=" | "/=" | "%=";

OperatorDecl => FunctionSignature OperatorDirective* WhereCaluse? Block;
OperatorDirective => "#symmetric" | FunctionDirectiveBase;
```

