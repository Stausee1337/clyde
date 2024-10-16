
# ROADMAP - The Project Continuation

## Obvious Problems / Flaws

- Conceptually simplify the Parser (Remove Pattern)
- Add typechecking for EVERY expression Cast, Tuple, ShorthandEnum, Range
    - Cast: check if certain cast is avaliable (for now: primitive casts)
    - Transmute: make sure types have the same size
    - Range: only numbers/chars; both have the same type
    - Tuple: 
- Implement support for enums
    - ShorthandEnum
- Support for `null` (finally)
- Add implementation for LOOPs: While, For
    - While: condition <-> bool, push loop rib, return type: never/void
    (never only if it never brakes NOT never returns, so we can recommend #never)
    - For: iterator needs to be array, dyn array, slice, range
- Implement SIMPLE Constant Evaluation (ArrayCapactiy)
    - only expressions <int, bool, char, str> literal 

## Add IR
Implementation should cover a simple, block based, statement based IR

Consider the following code:
```c
int main(str[] argv) {
    if len(argv) <= 1 {
        println("Usage: %s <file>", argv[0]);
        println("ERR: No argument was provided");
        return 1;
    }

    File file = file_open(argv[1], .Read);
    if file == null {
        return 1;
    }

    StringBuilder builder;
    read(&file, &builder);
    close(&file);

    println(builder_to_str(&builder));

    return 0;
}
```

This is a very nice code example and we can beatifully
see all the features version 1. of the clyde will probably have.

The genrated code would probably look smth like this:
```rust
fn main(%argv: Slice<str>) -> i32 {
    %file: File?;
    %builder: StringBuilder;
    bb0 [%argv] {
        %0 = call len(%argv)
        %1 = leq %0, const 1usize
        branch { on: %1 true: bb1, false: bb2 }
    }
    bb1 [%argv] {
        %2 = index %argv, const 0usize
        %3 = array 1
        index { array: %3, index: 0, value: %0 }
        %4 = ref %3
        call println(const $str0, %4)
        call println(const $str1)
        return 1i32
    }
    bb2 [%argv, %file] {
        %5 = index %argv, const 1usize
        %file = call file_open(%5, const 0 as OpenMode);
        %6 = eq %file, const 0 as File
        branch { on: %6 true: bb3, false: bb4 }
    }
    bb3 {
        return 1i32
    }
    bb4 [%file, %builder] {
        memset { dst: %builder, size: const $sizeof<StringBuilder>, val: 0 },
        %7 = ref %file
        %8 = ref %builder
        call read(%7, %8)
        %9 = ref %file
        call close(%9)
        %10 = ref %builder
        %11 = call builder_to_str(%10)
        call println(%11)
        return 0i32
    }
}
```
It will be very helpfull at bringing complex, nested logic down to
linear, branching control flow. The example IR shown here is obviously
extremly unoptimised

## Compile to Native Code

For compiling to native code, there are two options: emitting very simple,
crude x86 Assembly or using Cranelift as a backend.

### Cranelift
The usage and usefullness of the cranelift backend is very much dependent on
its simplicty and how easy translation from IR -> Cranelift IR will be

It is to consider though that cranelift backend emits highly optmized x86 has
a variety of instruction sets to chosse from already and probably will always
be the better API from emitting raw x86

### raw x86
If we turn to emitting raw, crude x86 instead, we'll probably focus on emitting
assembly rather then actual machine code.

The idea would be to write as set of small, stupid, non context-aware functions that
turn one IR intruction into a set of x86 instructions

```rust

%2 = index %argv, const 0usize
fn index_get<'asm, 'ir>(
    asm: &'asm AssebmlyCtxt, dst: &'ir mut ir::Reg, array: &'ir ir::Value, index: &'ir ir::Value) {
    .. // getting back to the real shit
}

```

## Further Roadmap

There is a list of things that still need to be done for version 1 (in that order)

1. FULL Support for generics
2. NEW lexer and parser; moving away from the generated parsers/lexers
3. Speeding up AST lookups (Owners, LocalIds)
4. Moving more information outside of the AST (particularly Resolve data)
5. [typechecking] Coercible types (eg. byte -> int, bool -> <number> conversions)
6. Multi-file support
7. Operator overloading
8. Default structs and values for enums
9. Implement Nullables (also in the parser)

