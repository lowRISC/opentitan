---
title: "Rust for Embedded C Programmers"
---

## Foreword

This document is intended as an introduction to Rust, targeted at engineers with deep exposure to embedded systems C, and little to no experience with C++ and no knowledge of Rust.
This document will:

*   Provide Rust analogues of everything in the embedded C toolkit.
*   Discuss how some of those analogues might be importantly different from C's.
*   Point out where Rust's memory and execution models materially differ from C.
*   Introduce Rust-specific features that are either key to using Rust at all or otherwise extremely useful (references, lifetimes, generics, traits).

While this document takes a casual approach to Rust, language-lawyer-ey notes are included in footnotes.
These are not required to get the most out of the document.

Playing with the compiler, and seeing what compiles, is a great way to learn Rust.
`rustc`, the standard Rust compiler, has excellent error messages.
Matt Godbolt's [Compiler Explorer](https://rust.godbolt.org/) is useful for getting a feel for the assembly that Rust produces.
The [Rust Playground](https://play.rust-lang.org/) can also be used to see what Rust code does when _executed_, though it is even more limited.

This document is written with a view towards embedded development.
We will not be discussing any non-embedded Rust features: see [https://rust-embedded.github.io/book/intro/no-std.html](https://rust-embedded.github.io/book/intro/no-std.html)[^1].

C++ users are cautioned: Rust shares a lot of terminology and concepts (ownership, lifetimes, destructors, polymorphism) with it, but Rust's realization of them tends to have significantly different semantics.
Experience in C++ should not be expected to translate cleanly.


## What is Rust? {#what-is-rust}

Rust is a general-purpose programming language with a focus on maximum programmer control and zero runtime overhead, while eliminating the sharp edges traditionally associated with such languages.
It is also sometimes called a "systems language".

Syntactically and philosophically, Rust most resembles C++ and ML (a family of functional programming languages), though semantically it is very different from both.
Rust is the first popular, well-supported language that provides absolute memory safety[^2] without the use of automatic reference counting or a garbage collector.
This is primarily achieved through a technology called the _borrow checker_, which uses source code annotations to statically prove that memory is not accessed after it is no longer valid, with no runtime checking.

Rust compiles to native code and rivals C and C++ for memory and compute performance, and can seamlessly integrate with anything using a C calling convention.
It also statically eliminates a large class of memory bugs associated with security vulnerabilities.
The Rust toolchain is built on LLVM, so all work towards LLVM performance is surfaced in Rust.

Rust also contains a special dialect called Unsafe Rust, which disables some static checking for the rare times when it is necessary to perform low-level operations.
We will make reference to this dialect throughout the document.


## The Rust Toolchain {#the-rust-toolchain}

A complete Rust toolchain consists of a few major parts:

*   `rustc`, the Rust compiler[^3].
*   `rustup`, the Rust toolchain installer[^4].
*   `cargo`, a build system for Rust (though rustc can be invoked directly or by other tools).
*   `std` and `core`, the standard libraries.

The Rust toolchain is on a six-week release cycle, similar to Chrome's: every six weeks, a release branch is cut as the next beta, and after six weeks it becomes the next stable.
Nightly Rust is cut from `master` every day; it is on nightly that unstable features can be enabled.
Some unstable features[^5] are very useful for embedded, so it is not uncommon for embedded Rust projects to use a nightly compiler.

`rustup` is used for managing Rust installations.
This is mostly necessary because Rust releases too frequently for operating system package managers to keep up, and projects can pin specific versions of Rust.
When the Rust toolchain is installed through rustup, components such as rustc and cargo will be aware of it; `rustc +nightly-2020-03-22` will defer to rustup to download and execute the `rustc` nightly built on March 22.
A file named `rust-toolchain` in a project directory can be used to the same effect.[^6]

Cargo is a build system/package manager for Rust.
It can build projects (that is, directories with a `Cargo.toml` file in them) and their dependencies automatically.
Individual units of compilation in Rust are called "crates", which are either static libraries[^7] (i.e., comparable to a `.a` file) or fully linked native binaries.
This is in contrast to C, where each `.c` file generates a separate object file.[^8] Rust also does not have headers, though it provides a module system for intra-crate code organization that will be discussed later on.
Tock boards are a good example of what a more-complex cargo file looks like: [https://github.com/tock/tock/blob/master/boards/opentitan/Cargo.toml](https://github.com/tock/tock/blob/master/boards/opentitan/Cargo.toml)

Some useful `cargo` subcommands include:
*   `cargo check` runs rustc's checks, but stops before it starts emitting code and optimizing it.
    This is useful for checking for errors during development.
*   `cargo build` builds a library or binary, depending on the crate type.
*   `cargo clippy` runs the Rust linter, Clippy.
*   `cargo doc --open` builds crate documentation and then opens it in the browser.
*   `cargo fmt` runs the Rust formatter[^9].

Also, the contents of the `RUSTFLAGS` environment variable are passed to `rustc`, as a mechanism for injecting flags.

The Rust standard library, like libc, is smaller in embedded environments.
The standard library consists of three crates: `core`[^10], `alloc`, and `std`.
`core`, sometimes called libcore, is all of the fundamental definitions, which don't rely on operating system support.
Nothing in `core` can heap-allocate.
`alloc` does not require OS support, but does require `malloc` and `free` symbols.
`std` is `core` + `alloc`, as well as OS APIs like file and thread support.
The `#[no_std]` pragma disables `std` and `alloc`, leaving behind `core`.
Throughout this document, we will only use `core` types, though we may refer to them through the `std` namespace (they're aliases).
That is, we may refer to `std::mem::drop`, though in `#[no_std]` code it must be named `core::mem::drop`.

rustc has a number of flags. The most salient of these are:



*   `--emit asm` and `--emit llvm-ir`, useful for inspecting compiler output.
*   `--target`, which sets the cross-compilation target.
     It has a similar role to Clang's `-target`, `-march`, and `-mabi` flags.
     It accepts a target definition (which in many cases resembles an LLVM target triple) that defines the platform.
     For example, OpenTitan software uses the `riscv32imc-unknown-none-elf` target.
     Using a target that isn't the host target (e.g.,`x86_64-unknown-linux-musl`) requires installing the corresponding standard library build with `rustup component install rust-std-<target>`.
     See `rustc --print targets`.
     `--target` is also accepted directly by Cargo, unlike most rustc flags.
*   `-C link-arg`, equivalent to Clang's `-T`.
*   `-C opt-level`, equivalent to Clang's `-O` (we mostly use `-C opt-level=z` for embedded).
*   `-C lto`, equivalent to Clang's `-flto`.
*   `-C force-frame-pointers`, equivalent to Clang's `-fno-omit-frame-pointer`.
*   `-D warnings` is roughly equivalent to `-Werror`.

Other interesting flags can be found under `rustc -C help` and, on nightly, under `rustc -Z help`.


## Part I: Rewriting your C in Rust {#part-i-rewriting-your-c-in-rust}

Before diving into Rust's specific features, we will begin by exploring how C concepts map onto Rust, as well as Unsafe Rust, a dialect of Rust that is free of many of Rust's restrictions, but also most of its safety guarantees.


### Types {#types}

Rust and C have roughly the same approach to types, though Rust has few implicit conversions (for example, it lacks integer promotion like C).
In this section, we will discuss how to translate C types into Rust types.


#### Integers {#integers}

Rust lacks C's `int`, `long`, `unsigned`, and other types with an implementation-defined size.
Instead, Rust's primitive integer types are exact-size types: `i8`, `i16`, `i32`, `i64`, and `i128` are signed integers of 8, 16, 32, 64, and 128 bits, respectively, while `u8`, `u16`, `u32`, `u64`, and `u128` are their unsigned variants.
Rust also provides `isize` and `usize`, which correspond to `intptr_t` and `uintptr_t`[^11].
Alignment requirements are exactly the same as in C.

Rust supports all of the usual binary operations on all of its integer types[^12][^13], though you can't mix different types when doing arithmetic, and, unlike in C, there is no integer promotion.
Overflow in Rust is different from C[^14]: it is implementation-defined, and must either crash the program[^15] or wrap around[^16].
Casting is done with the `as` keyword, and behaves exactly the same way as in C: `(uint8_t) x` is written `x as u8`. Integer types never implicitly convert between each other, even between signed and unsigned variants.

Rust has the usual integer literals: `123` for decimal, `0xdead` for hex, `0b1010` for binary, and `0o777` for octal.
Underscores may be arbitrarily interspersed throughout an integer literal to separate groups of digits: `0xdead_beef`, `1_000_000`.
They may also be suffixed with the name of a primitive integer type to force their type: `0u8`, `0o777i16`, `12_34_usize`; they will otherwise default to whatever type inference (more on this later) chooses, or `i32` if unconstrained.

Rust also has a dedicated `bool` type.
It is not implicitly convertible with integers, and is otherwise a `u8` that is guaranteed to have either the value `0x00` or `0x01`[^17], with respective literals `false` and `true`.
`bool` supports all of the bitwise operations, and is the only type compatible with short-circuiting `&&` and `||`.
It is also the only type that can be used in `if` and `while` conditions.

Integers have an extensive set of built-in operations for bit-twiddling, exposed as methods, such as `x.count_zeros()` and `x.next_power_of_two()`[^18].
See [https://doc.rust-lang.org/std/primitive.u32.html](https://doc.rust-lang.org/std/primitive.u32.html) for examples.

#### Structs and Tuples {#structs-and-tuples}

Structs are declared almost like in C:
```rust
struct MyStruct {
  pub foo: i32,
  pub bar: u8,
}
```
Rust has per-field visibility modifiers (`pub`); we'll give visibility a more thorough treatment later.

Struct values can be created using an analogue of C's designated initialization[^19] syntax:
```rust
MyStruct { foo: -42, bar: 0xf, }
```

Rust structs are not laid out like C structs, though; in fact, Rust does not specify the layout of its structs[^20].
A C struct can be specified in Rust using the `#[repr(C)]` attribute:
```rust
#[repr(C)]
struct MyCStruct {
  a: u8,
  b: u32,
  c: u8,
}
```
This is guaranteed to lay out fields in declaration order, adding padding for alignment.
`#[repr(Rust)]` is the implicit default.
`#[repr(packed)]` is analogous to `__attribute__((packed))`, and will not produce any padding[^21].
The alignment of the whole struct can be forced to a larger value using `#[repr(align(N))]`, similar to `_Alignas`.

Fields can be accessed using the same dot syntax as C: `my_struct.foo`, `my_struct.bar = 5;`.

Rust also provides "tuple-like structs", which are structs with numbered, rather than named, fields:
```rust
struct MyTuple(pub u32, pub u8);
```

Fields are accessed with a similar dot syntax: `tuple.0`, `tuple.1`, and are constructed with function-call-like syntax: `MyTuple(1, 2)`.
Other than syntax, they are indistinguishable from normal structs. The fields on a tuple-like struct may be omitted to declare a zero-byte[^22] struct:
```rust
struct MyEmpty;
```

Anonymous versions of tuples are also available: `(u32, u8)`.
These are essentially anonymous structs with unnamed fields.
The empty tuple type, `()`, is called "unit", and serves as Rust's `void` type (unlike `void`, `()` has exactly one value, also named `()`, which is zero-sized).
Rust has another void-like type, `!`, which we'll discuss when we talk about functions.

If every field of a struct can be compared with `==`, the compiler can generate an equality function for your struct:
```rust
#[derive(PartialEq, Eq)]
struct MyStruct {
  a: u32,
  b: u8,
}
```

This makes it possible to use `==` on `MyStruct` values, which will just perform field-wise equality.
The same can be done for ordering operations like `<` and `>=`: `#[derive(PartialOrd, Ord)]` will define comparison functions that compare structs lexicographically.

#### Enums and Unions

Much like C, Rust has enumerations for describing a type with a fixed set of values:
```rust
enum MyEnum {
    Banana, Apple, Pineapple,
}
```

Unlike C, though, `MyEnum` is a real type, and not just an alias for an integer type.
Also unlike C, the enum's variants are not dumped into the global namespace, and must instead be accessed through the enum type: `MyEnum::Banana`.
Note that, unlike structs, the variants of an enum are automatically public.

While Rust does represent enum values with integers (these integers are called _discriminants_), the way they're laid out is unspecified.
To get an enum whose discriminants are allocated like in C, we can employ a `repr` attribute:
```rust
#[repr(C)]
enum MyCEnum {
  Banana = 0,
  Apple = 5,
  Pineapple = 7,
}
```
Unlike C, though, Rust will only guarantee discriminant values that are explicitly written down.
Such enums may be safely cast into integer types (like `MyCEnum::Apple as u32`), but not back: the compiler always assumes that the underlying value of a `MyCEnum` is `0`, `5`, or `7`, and violating this constraint is Undefined Behavior (UB)[^23].
If we want to require that an enum is an exact integer width, we can use `#[repr(T)]`, where `T` is an integral type like `u16` or `i8`.

Unions in Rust are a fairly recent feature, and are generally not used for much in normal code.
They are declared much like structs:
```rust
union MyUnion {
  pub foo: i32,
  pub bar: u8,
}
```
and created much like structs:
```rust
MyUnion { bar: 0xa, }  // `bar` is the active variant.
```

Assigning to union variants is the same as in structs, but reading a variant requires Unsafe Rust, since the compiler can't prove that you're not reading uninitialized or invalid data[^24], so you'd need to write
```rust
unsafe { my_union.bar }  // I assert that bar is the active variant.
```
Unions also have restrictions on what types can be used as variants, due to concerns about destructors.

Since unions are so useful in C, but utterly unsafe, Rust provides built-in _tagged unions_[^25], which are accessed through the `enum` syntax:
```rust
enum MyEnum {
  FooVariant { foo: i32 },
  BarVariant(u8),
}
```

Tagged-union enum variants use the same syntax as Rust structs; enum consists of a tag value (the discriminant) big enough to distinguish between all the variants, and a compiler-tracked union of variants.
However, effective use of such enums requires _pattern matching_, which requires its own section to explain.
We'll see these enums again when we discuss patterns.

Just like with structs, `#[derive]` can be used on enums to define comparison operators, which are defined analogously to the struct case.

#### Arrays {#arrays}

Rust arrays are just C arrays: inline storage of a compile-time-known number of values.
`T[N]` in C is spelled `[T; N]` in Rust.
Arrays are created with `[a, b, c]` syntax, and an array with lots of copies of the same value can be created using `[0x55u8; 1024]`[^26].
A multi-dimensional array can be declared as an array of arrays: `[[T; N]; M]`.

Array elements can be accessed with `x[index]`, exactly like in C.
Note, however, that Rust automatically inserts bounds checks around every array access[^27]; failing the bounds check will trigger a panic in the program.
Unsafe Rust can be used to cheat the bounds check when it is known (to the programmer, not rustc!) to be unnecessary to perform it, but when it is performance critical to elide it.

Rust arrays are "real" types, unlike in C. They can be passed by value into functions, and returned by value from functions.
They also don't decay into pointers when passed into functions.

#### Pointers {#pointers}

Like every other embedded language, Rust has pointers.
These are usually referred to as _raw pointers_, to distinguish them from the myriad of smart pointer types.
Rust spells `T*` and `const T*` as `*mut T` and `*const T`.
Unlike in C, pointers do not need to be aligned to their pointee type[^28] until they are dereferenced (like C, Rust assumes that all pointer reads/writes are well-aligned).

Note that C's type-based strict aliasing does not exist in Rust[^29].
As we'll learn later, Rust has different aliasing rules for references that are both more powerful and which the compiler can check automatically.

`usize`, `isize`, and all pointer types may be freely cast back and forth.[^30] Null pointers may be created using the `std::ptr::null()` and `std::ptr::null_mut()` functions[^31].
Rust pointers do not support arithmetic operators; instead, a method fills this role: instead of `ptr + 4`, write `ptr.offset(4)`.
Equality among pointers is simply address equality.

Pointers can be dereferenced with the `*ptr` syntax[^32], though this is Unsafe Rust and requires uttering `unsafe`.
When pointers are dereferenced, they must be well-aligned and point to valid memory, like in C; failure to do so is UB.
Unlike in C, the address-of operator, `&x`, produces a reference[^33], rather than a pointer.
`&x as *const T` will create a pointer, instead.

Pointer dereference is still subject to move semantics, like in normal Rust[^34].
the `read()` and `write()` methods on pointers can be used to ignore these rules[^35].
`read_unaligned()`[^36] and `write_unaligned()`[^37] can be used to perform safe[^38] unaligned access, and `copy_to()`[^39] and `copy_nonoverlapping_to()`[^40] are analogous to `memmove()` and `memcpy()`, respectively.
See [https://doc.rust-lang.org/std/primitive.pointer.html](https://doc.rust-lang.org/std/primitive.pointer.html) for other useful pointer methods.
Volatile operations are also performed using pointer methods, which are discussed separately later on.

Since all of these operations dereference a pointer, they naturally are restricted to Unsafe Rust.

As we will discover later, Rust has many other pointer types beyond raw pointers.
In general, raw pointers are only used in Rust to point to potentially uninitialized memory[^41] and generally denote _addresses_, rather than references to actual memory.
For that, we use _references_, which are discussed much later.

We will touch on function pointers when we encounter functions.


### Items {#items}

Like C, Rust has globals and functions.
These, along with the type definitions above, are called _items_ in the grammar, to avoid confusion with C's declaration/definition distinction.
Unlike C, Rust does not have forward declaration or declaration-order semantics; everything is visible to the entire file.
Items are imported through dedicated import statements, rather than textual inclusion; more on this later.


#### Constants and Globals {#constants-and-globals}

Rust has dedicated syntax for compile-time constants, which serve the same purpose as `#define`d constants do in C.
Their syntax is
```rust
const MY_CONSTANT: u32 = 0x42;
```
The type is required here, and the right-hand side must be a _constant expression_, which is roughly any combination of literals, numeric operators, and `const fn`s (more on those in a moment).

Constants do not exist at runtime.
They can be thought of best as fixed expressions that get copy+pasted into wherever they get used, similar to `#define`s and `enum` declarators in C.
It is possible to take the address of a constant, but it is not guaranteed to be consistent.[^42]

Globals look like constants, but with the keyword `static`[^43]:
```rust
static MY_GLOBAL: u8 = 0x00;
static mut MY_MUTABLE_GLOBAL: Foo = Foo::new();
```
Globals are guaranteed to live in `.rodata`, `.data`, or `.bss`, depending on their mutability and initialization.
Unlike constants, they have unique addresses, but as with constants, they must be initialized with constant expressions.[^44]

Mutable globals are particularly dangerous, since they can be a source of data races in multicore systems.
Mutable globals can also be a source other racy behavior due to IRQ control flow.
As such, reading or writing to a mutable global, or creating a reference to one, requires Unsafe Rust.


#### Functions {#functions}

In C and Rust, functions are the most important syntactic construct. Rust declares functions like so:
```rust
fn my_function(x: u32, y: *mut u32) -> bool {
  // Function body.
}
```
The return type, which follows the `->` token, can be omitted when it is `()` ("unit", the empty tuple), which serves as Rust's equivalent of the `void` type.
Functions are called with the usual `foo(a, b, c)` syntax.

The body of a function consists of a list of statements, potentially ending in an expression; that expression is the function's return value (no `return` keyword needed).
If the expression is missing, then `()` is assumed as the return type. Items can be mixed in with the statements, which are local to their current scope but visible in all of it.

Rust functions can be marked as `unsafe fn`.
This means the function cannot be called normally, and must instead be called using Unsafe Rust.
The body of an `unsafe fn` behaves like an `unsafe` block; we'll go more into this when we discuss Unsafe Rust in detail.

Rust functions have an unspecified calling convention[^45].
To declare a function with a different calling convention, the function is declared `extern "ABI" fn foo()`, where ABI is a supported ABI.
`"C"` is the only one we really care about, which switches the calling convention to the system's C ABI. The default, implicit calling convention is `extern "Rust"`[^46].

Marking functions as `extern` does not disable name mangling[^47]; this must be done by adding the `#[no_mangle]` attribute to the function.
Unmangled functions can then be called by C, allowing a Rust library to have a C interface.
A mangled, `extern "C"` function's main use is to be turned into a function pointer to pass to C.

Function pointer types look like functions with all the variable names taken out: `fn(u32, *mut u32) -> bool`.
Function pointers cannot be null, and must always point to a valid function with the correct ABI.
Function pointers can be created by implicitly converting a function into one (no `&` operator).
Function pointers also include the `unsafe`-ness and `extern`-ness of a function: `unsafe extern "C" fn() -> u32`.

Functions that never return have a special return type `!`, called the "never type".
This is analogous to the `noreturn` annotation in C.
However, using an expression of type `!` is necessarily dead code, and, as such, `!` will implicitly coerce to all types (this simplifies type-checking, and is perfectly fine since this all occurs in provably-dead code).

Functions can also be marked as `const`.
This makes the function available for constant evaluation, but greatly restricts the operations available.
The syntax available in `const` functions increases in every release, though.
Most standard library functions that can be `const` are already `const`.


#### Macros {#macros}

Rust, like C, has macros.
Rust macros are much more powerful than C macros, and operate on Rust syntax trees, rather than by string replacement.
Macro calls are differentiated from function calls with a `!` following the macro name.
For example, `file!()` expands to a string literal with the file name.
To learn more about macros, see [https://danielkeep.github.io/tlborm/book/index.html](https://danielkeep.github.io/tlborm/book/index.html).


#### Aliases {#aliases}

Rust has `type`, which works exactly like `typedef` in `C`.
Its syntax is
```rust
type MyAlias = u32;
```

### Expressions and Statements {#expressions-and-statements}

Very much unlike C, Rust has virtually no statements in its grammar: almost everything is an expression of some kind, and can be used in expression context.
Roughly speaking, the only statement in the language is creating a binding:
```rust
let x: u32 = foo();
```
The type after the `:` is optional, and if missing, the compiler will use all information in the current scope, both before and after the `let`, to infer one[^48].

An expression followed by a semicolon simply evaluates the expression for side-effects, like in other languages[^49].
Some expressions, like `if`s, `whiles`, and `for`s, don't need to be followed by a semicolon.
If they are not used in an expression, they will be executed for side-effects.

`let` bindings are immutable by default, but `let mut x = /* ... */;` will make it mutable.

Like in C, reassignment is an expression, but unlike in C, it evaluates to `()` rather than to the assigned value.

Like in almost all other languages, literals, operators, function calls, variable references, and so on are all standard expressions, which we've already seen how Rust spells already.
Let's dive into some of Rust's other expressions.


#### Blocks {#blocks}

Blocks in Rust are like better versions of C's blocks; in Rust, every block is an expression.
A block is delimited by `{ }`, consists of a set of a list of statements and items, and potentially an ending expression, much like a function.
The block will then evaluate to the final expression. For example:
```rust
let foo = {
  let bar = 5;
  bar ^ 2
};
```
Blocks are like local functions that execute immediately, and can be useful for constraining the scope of variables.

If a block does not end in an expression (that is, every statement within ends in a semicolon), it will implicitly return `()`, just like a function does.
This automatic `()` is important when dealing with constructs like `if` and `match` expressions that need to unify the types of multiple branches of execution into one.

#### Conditionals: `if` and `match` {#conditionals-if-and-match}

Rust's `if` expression is, syntactically, similar to C's. The full syntax is
```rust
if cond1 {
  // ...
} else if cond2 {
  // ...
} else {
  // ...
}
```

Conditions must be expressions that evaluate to `bool`.
A conditional may have zero or more `else if` clauses, and the `else` clause is optional.
Because of this, Rust does not need (and, thus, does not have) a ternary operator:
```rust
let x = if c { a } else { b };
```

Braces are required on `if` expressions in Rust.

`if` expressions evaluate to the value of the block that winds up getting executed.
As a consequence, all blocks must have the same type[^50].
For example, the following won't compile, because an errant semicolon causes type checking to fail:
```rust
if cond() {
  my_int(4)   // Type is i32.
} else {
  my_int(7);  // Type is (), due to the ;
}
```
`i32` and `()` are different types, so the compiler can't unify them into an overall type for the whole `if`.

In general, it is a good idea to end all final expressions in `if` clauses with a semicolon, unless its value is needed.

Like C, Rust has a `switch`-like construct called `match`. You can match integers:
```rust
let y = match x {
  0 => 0x00,       // Match 0.
  1..=10 => 0x0f,  // Match all integers from 1 to 10, inclusive.
  _ => 0xf0,       // Match anything, like a `default:` case.
};
```
Like `if` expressions, `match` expressions produce a value.
The syntax `case val: stuff; break;` roughly translates into `val => stuff,` in Rust.
Rust calls these case clauses "match arms"[^51].

`match` statements do not have fallthrough, unlike C.
In particular, only one arm is ever executed.
Rust, however, allows a single match arm to match multiple values:
```rust
match x {
  0 | 2 | 4 => /* ... */,
  _ => /* ... */,
}
```

Rust will statically check that every possible case is covered.
This is especially useful when matching on an enum:
```rust
enum Color { Red, Green, Blue, }
let c: Color = /* ... */;
match c {
  Color::Red =>   /* ... */,
  Color::Green => /* ... */,
  Color::Blue =>  /* ... */,
}
```
No `_ =>` case is required, like a `default:` would in C, since Rust statically knows that all cases are covered (because enums cannot take on values not listed as a variant).
If this behavior is not desired in an enum (because more variants will be added in the future), the `#[non_exhaustive]` attribute can be applied to an enum definition to require a default arm.

We will see later that pattern matching makes `match` far more powerful than C's `switch`.


#### Loops: `loop` and `while` {#loops-loop-and-while}

Rust has three kinds of loops: `loop`, `while`, and `for`.
`for` is not a C-style `for`, so we'll discuss it later.
`while` is simply the standard C `while` loop, with slightly different syntax:
```rust
while loop_condition { /* Stuff. */ }
```
It can be used as an expression, but it always has type `()`; this is most notable when it is the last expression in a block.

`loop` is unique to Rust; it is simply an infinite loop[^52]:
```rust
loop { /* Stuff. */ }
```
Because infinite loops can never end, the type of the `loop` expression (without a `break` in it!) is `!`, since any code after the loop is dead.
Having an unconditional infinite loop allows Rust to perform better type and lifetime analysis on loops.
Under the hood, all of Rust's control flow is implemented in terms of `loop`, `match`, and `break`.


#### Control Flow {#control-flow}

Rust has `return`, `break`, and `continue`, which have their usual meanings from C.
They are also expressions, and, much like `loop {}`, have type `!` because all code that follows them is never executed (since they yank control flow).

`return x` exits a function early with the value `x`.
`return` is just syntax for `return ()`.
`break` and `continue` do the usual things to loops.

All kinds of loops may be annotated with labels (the only place where Rust allows labels):
```rust
'a: loop {
  // ...
}
```
`break` and `continue` may be used with those labels (e.g. `break 'a`), which will break or continue the enclosing loop with that label (rather than the closest enclosing loop).
While C lacks this feature, most languages without `goto` have it.

It is also possible to `break`-with-value out of an infinite loop, which will cause the `loop` expression to evaluate to that value, rather than `!`[^53].
```rust
let value = loop {
  let attempt = get();
  if successful(attempt) {
    break attempt;
  }
};
```


### Talking to C {#talking-to-c}

One of Rust's great benefits is mostly-seamless interop with existing C libraries.
Because Rust essentially has no runtime, Rust types that correspond to C types can be trivially shared, and Rust can call C functions with almost no overhead[^54].
The names of external symbols can be "forward-declared" using an `extern` block, which allows Rust to name, and later link with, those symbols:
``` rust
extern "C" {
  fn malloc(bytes: usize) -> *mut u8;
  static mut errno: i32;
}
```
When the ABI specified is `"C"`, it can be left off; `extern {}` is implicitly `extern "C" {}`.

It is the linker's responsibility to make sure those symbols wind up existing.
Also, some care must be taken with what types are sent over the boundary.
See [https://doc.rust-lang.org/reference/items/external-blocks.html](https://doc.rust-lang.org/reference/items/external-blocks.html) for more details.


### Analogues of other functionality {#analogues-of-other-functionality}

#### Volatile {#volatile}

Rust does not have a `volatile` qualifier.
Instead, volatile reads can be performed using the `read_volatile()`[^55] and `write_volatile()`[^56] methods on pointers, which behave exactly like volatile pointer dereference in C.

Note that these methods work on types wider than the architecture's volatile loads and stores, which will expand into a series of volatile accesses, so beware.
The same caveat applies in C: `volatile uint64_t` will emit multiple accesses on a 32-bit machine.


#### Inline Assembly {#inline-assembly}

Rust does not quite support inline assembly yet.
Clang's inline assembly syntax is available behind the unstable macro `llvm_asm!()`, which will eventually be replaced with a Rust-specific syntax that better integrates with the language.
`global_asm!()` is the same, but usable in global scope, for defining whole functions.
Naked functions can be created using `#[naked]`. See [https://doc.rust-lang.org/1.8.0/book/inline-assembly.html](https://doc.rust-lang.org/1.8.0/book/inline-assembly.html).

[Note that this syntax is currently in the process of being redesigned and stabilized.](https://blog.rust-lang.org/inside-rust/2020/06/08/new-inline-asm.html)

#### Bit Casting {#bit-casting}

Rust provides a type system trap-door for bitcasting any type to any other type of the same size:
```rust
let x = /* ... */;
let y = std::mem::transmute<A, B>(x);
```
This trap-door is extremely dangerous, and should only be used when `as` casts are insufficient.
The primary embedded-relevant use-case is for summoning function pointers from the aether, since Rust does not allow casting raw pointers into function pointers (since the latter are assumed valid).

[https://doc.rust-lang.org/std/mem/fn.transmute.html](https://doc.rust-lang.org/std/mem/fn.transmute.html) has a list of uses, many of which do not actually require transmute.


#### Linker Shenanigans and Other Attributes {#linker-shenanigans-and-other-attributes}

Below are miscellaneous attributes relevant to embedded programming.
Many of these subtly affect linker/optimizer behavior, and are very much in the "you probably don't need to worry about it" category.

*   `#[link_section = ".my_section"]` is the rust spelling of `__attribute__((section(".my_section")))`, which will stick a symbol in the given ELF (or equivalent) section.
*   `#[used]` can be used to force a symbol to be kept by the linker[^57] (this is often done in C by marking the symbol as `volatile`). The usual caveats for `__attribute__((used))`, and other linker hints, apply here.
*   `#[inline]` is analogous to C's `inline`, and is merely a hint; `#[inline(always)]` and `#[inline(never)]` will always[^58] or never be inlined, respectively.
*   `#[cold]` can also be used to pessimize inlining for functions that are unlikely to ever be called.


## Part II: Rust-Specific Features {#part-ii-rust-specific-features}

The previous part established enough vocabulary to take roughly any embedded C program and manually translate it into Rust.
However, those Rust programs are probably about as safe and ergonomic as the C they came from.
This section will focus on introducing features that make Rust safer and easier to write.


### Ownership {#ownership}

Double-free or, generally, double-use, are a large class of insidious bugs in C, which don't look obviously wrong at a glance:
```c
// `handle` is a managed resource to a peripheral, that should be
// destroyed to signal to the hardware that the resource is not in use.
my_handle_t handle = new_handle(0x40000);
use_for_scheduling(handle);  // Does something with `handle` and destroys it.
// ... 200 lines of scheduler code later ...
use_for_scheduling(handle);  // Oops double free.
```
Double-free and use-after-free are a common source of crashes and security vulnerabilities in C code.
Let's see what happens if we were to try this in Rust.

Consider the equivalent code written in Rust:
```rust
let handle = new_handle(0x40000);
use_for_scheduling(handle);
// ...
use_for_scheduling(handle);
```

If you then attempt to compile this code, you get an error:
```rust
error[E0382]: use of moved value: `handle`
  --> src/main.rs:10:24
   |
7  |     let handle = new_handle(0x40000);
   |         ------ move occurs because `handle` has type `Handle`,
   |                which does not implement the `Copy` trait
8  |     use_for_scheduling(handle);
   |                        ------ value moved here
9  |     // ...
10 |     use_for_scheduling(handle);
   |                        ^^^^^^ value used here after move
```

Use-after-free errors (and double-free errors) are impossible in Safe Rust.
This particular class of errors (which don't directly involve pointers) are prevented by _move semantics_.
As the error above illustrates, using a variable marks it as having been "moved from": the variable is now an empty slot of uninitialized memory.
The compiler tracks this statically, and compilation fails if you try to move out again.
The variable in which a value is currently stored is said to be its "owner"[^59]; an owner is entitled to hand over ownership to another variable[^60], but may only do so once.

The error also notes that "`Handle` does not implement the `Copy` trait."
Traits proper are a topic for later; all this means right now is that `Handle` has move semantics (the default for new types).
Types which _do_ implement `Copy` have _copy semantics_; this is how all types passed-by-value in C behave: in C, passing a struct-by-value always copies the whole struct, while passing a struct-by-reference merely makes a copy of the pointer to the struct.
This is why moves are not relevant when handling integers and raw pointers: they're all `Copy` types.

Note that any structs and enums you define won't be `Copy` by default, even if all of their fields are.
If you want a struct whose fields are all `Copy` to also be `Copy`, you can use the following special syntax:
```rust
#[derive(Clone, Copy)]
struct MyPodType {
  // ...
}
```

Of course, the copy/move distinction is something of a misnomer: reassignment due to copy and move semantics compiles to the same `memcpy` or register move code.
The distinction is purely for static analysis.


### References and Lifetimes {#references-and-lifetimes}

Another class of use-after-free involves stack variables after the stack is destroyed.
Consider the following C:
```c
const int* alloc_int(void) {
  int x = 0;
  return &x;
}
```
This function is obviously wrong, but such bugs, where a pointer outlives the data it points to, are as insidious as they are common in C.

Rust's primary pointer type, _references_, make this impossible.
References are like raw pointers, except they are always well-aligned, non-null, and point to valid memory; they also have stronger aliasing restrictions than C pointers.
Let's explore how Rust achieves this last guarantee.

Consider the following Rust program:
```rust
fn alloc_int() -> &i32 {
  let x = 0i32;
  &x
}
```
This program will fail to compile with a cryptic error: `missing lifetime specifier`.
Clearly, we're missing something, but at least the compiler didn't let this obviously wrong program through.

A lifetime, denoted by a symbol like `'a`[^61] (the apostrophe is often pronounced "tick"), labels a region of source code[^62].
Every reference in Rust has a lifetime attached, representing the region in which a reference is known to point to valid memory: this is specified by the syntax `&'a i32`: reference to `i32` during `'a`.
Lifetimes, much like types, do not exist at runtime; they only exist for the compiler to perform _borrow checking_, in which the compiler ensures that references only exist within their respective lifetimes.
A special lifetime, `'static` represents the entire program.
It is the lifetime of constants and global variables.

Consider the following Rust code:
```rust
let x: i32 = 42;
let y: &'a i32 = &x;  // Start of 'a.
use_reference(y);
use_value(x);  // End of 'a, because x has been moved.
use_reference(y);  // Error: use of y outside of 'a.
```
Reference lifetimes start when the reference is taken, and end either when the lifetime goes out of scope or when the value referenced is moved.
Trying to use the reference outside of the lifetime is an error, since it is now a dangling pointer.

Rust often refers to references as _borrows_: a reference can borrow a value from its owner for a limited time (the lifetime), but must return it before the owner gives the value up to someone else.
It is also possible for a reference to be a borrow of a borrow, or a _reborrow_: it is always possible to create a reference with a shorter lifetime but with the same value as another one.
Reborrowing is usually performed implicitly by the compiler, usually around call sites, but can be performed explicitly by writing `&*x`.

Lifetimes can be elided in most places they are used:
```rust
fn get_field(m: &MyStruct) -> &u32 {
  &m.field  // For references, unlike for raw pointers, . acts the same way -> does in C.
}
```
Here, the compiler assumes that the lifetime of the return type should be the same as the lifetime of the `m`[^63].
However, we can write this out explicitly:
```rust
fn get_field<'a>(m: &'a MyStruct) -> &'a u32 { /* ... */ }
```
The `<'a>` syntax introduces a new named lifetime for use in the function signature, so that we can explicitly tell the compiler "these two references have the same lifetime".
This is especially useful for specifying many lifetimes, when the compiler can't make any assumptions:
```rust
fn get_fields<'a, 'b>(m1: &'a MyStruct, m2: &'b MyStruct) -> (&'a u32, &'b u32) {
  (&m1.field, &m2.field)
}
```
Now we can try to fix our erroneous stack-returning function.
We need to introduce a new lifetime for this function, since there's no function arguments to get a lifetime from:
```rust
fn alloc_int<'a>() -> &'a i32 {
  let x = 0i32;
  &x
}
```
This now gives us a straightforward error, showing the borrow-checking prevents erroneous stack returns:
```rust
error[E0515]: cannot return reference to local variable `x`
 --> src/lib.rs:9:3
  |
9 |   &x
  |   ^^ returns a reference to data owned by the current function
```

This `<'a>` syntax can also be applied to items like structs: If you're creating a type containing a reference, the `<'a>` is required:
```rust
struct MyRef<'a> {
  meta: MyMetadata,
  ptr: &'a u32,  // Lifetime elision not allowed here.
}
```

Rust's references come in two flavors: shared and unique.
A shared reference, `&T`, provides immutable access to a value of type `T`, and can be freely duplicated: `&T` is `Copy`.
A unique reference, `&mut T`, provides mutable access to a value of type `T`, but is subject to Rust's aliasing rules, which are far more restrictive than C's strict aliasing, and can't be turned off.

There can only be one `&mut T` active for a given value at a time.
This means that no other references may be created within the lifetime of the unique reference.
However, a `&mut T` may be reborrowed, usually for passing to a function.
During the reborrow lifetime, the original reference cannot be used.
This means the following code works fine:
```rust
fn do_mut(p: &mut Handle) { /* ... */ }

let handle: &mut Handle = /* ... */;
do_mut(handle);  // Reborrow of handle for the duration of do_mut.
// handle is valid again.
do_mut(handle);  // Reborrow again.
```
In other words, Rust does not have a safe equivalent to `int*`; it only has equivalents for `const int*` and `int* restrict` ... plus casting away `const` is instant Undefined Behavior[^64].
Rust will aggressively collapse loads and stores, and assume that no mutable references alias for the purpose of its alias analysis.
This means more optimization opportunities, without safe code needing to do anything.[^65]

Finally, it should go without saying that references are only useful for main memory; Rust is entitled to generate spurious loads and stores for (possibly unused!) references[^66], so MMIO should be performed exclusively through raw pointers.

[https://doc.rust-lang.org/book/ch10-03-lifetime-syntax.html](https://doc.rust-lang.org/book/ch10-03-lifetime-syntax.html) elaborates further on the various lifetime rules.


#### Operations on References {#operations-on-references}

Rust references behave much more like scalar values than like pointers (borrow-checking aside).
Because it is statically known that every reference, at all times, points to a valid, initialized value of type `T`, explicit dereferencing is elided most of the time (though, when necessary, they can be dereferenced: `*x` is an lvalue that can be assigned to).

Rust does not have a `->` operator, but, for `x: &T`, the dot operator behaves as if `x` were a `T`.
If `field` is a field of `T`, for example, `x.field` is the lvalue of `field` (which would be spelled `x->field` in C).
This applies even for heavily nested references: the dot operator on `&&&T` will trigger three memory lookups.
This is called the "auto-deref" behavior.

Equality of references is defined as equality of underlying values: `x == y`, for `x: &T` and `y: &T`, becomes `*x == *y`.
Pointer equality is still possible with `std::ptr::eq(x, y)`.
References can be coerced into raw pointers: `x as *const T`, and compared directly.


### Methods {#methods}

While Rust is not an object-oriented language, it does provide a mechanism for namespacing functions under types: `impl` (for implementation) blocks.
These also allow you to make use of Rust's visibility annotations, to make implementation details and helpers inaccessible to outside users.

Here's an example of a type with methods.
```rust
pub struct Counter(u64);  // Non-public field!
impl MyType {
  /// Creates a new `Counter`.
  pub fn new() -> Self {
    Counter(0)
  }

  /// Private helper.
  fn add(&mut self, x: u64) {
    self.0 += x;
  }

  /// Get the current counter value.
  pub fn get(&self) -> u64 {
    self.0
  }

  /// Increment the counter and return the previous value.
  pub fn inc(&mut self) -> u64 {
    let prev = self.get();
    self.add(1);
    prev
  }

  /// Consumes the counter, returning its final value.
  pub fn consume(self) -> u64 {
    self.get()
  }
}
```
Outside modules cannot access anything not marked as `pub`, allowing us to enforce an invariant on `Counter`: it is monotonic.
Let's unpack the syntax.

Functions in an `impl` block are called "inherent functions" or "methods", depending on whether they take a `self` parameter.
Inherent functions don't take a `self`, and are called like `Counter::new()`[^67].

A `self` parameter is a parameter named `self` (which is a keyword) and having a type involving `Self`[^68] (another keyword, which is a type alias for the type the `impl` block is for), such as `&Self`[^69].
The syntax `self`, `&self`, `mut self`, and `&mut self` are sugar for the common forms `self: Self`, `self: &Self`, `mut self: Self` and `self: &mut Self`, representing self-by-value, self-by-reference, self-by-mut-value, and self-by-mut-reference.

Methods can, thus, be called like so: `my_counter.inc()`.
Methods are really just normal functions: you could also have called this like `Counter::inc(&mut my_counter)`.
Note that calling a function that takes `&self` or `&mut self` triggers a borrow of the receiving type; if a `&self` function is called on a non-reference value, the value will have its address taken, which gets passed into the method.

`impl` blocks, like other items, can be parameterized by lifetimes.
In order to add methods to a struct with a reference in it, the following syntax can be used:
```rust
impl<'a> MyStruct<'a> { /* ... */ }
```
If `'a` is never actually used inside the `impl` block, this can be written using a _placeholder lifetime_:
```rust
impl MyStruct<'_> { /* ... */ }
```
As we've already seen, many primitive types have methods, too; these are defined in special `impl` blocks in the standard library.


### Slices and `for` {#slices-and-for}

References also do not allow for pointer arithmetic, so a `&u32` cannot be used to point to a buffer of words.
Static buffers can be passed around as arrays, like `&[u32; 1024]`, but often we want to pass a pointer to contiguous memory of a runtime-known value.
_Slices_ are Rust's solution to pointer+length.

A slice of `T` is the type `[T]`; this type is most like a "flexible array member" in C:
```rust
struct slice {
  size_t len;
  T values[];
}
```
Then, a `slice*` would point to a length followed by that many `T`s; it can't reasonably exist except behind a pointer.
Similarly, `[T]` is what Rust calls a dynamically sized type[^70], which needs to exist behind a reference: it is much more common to see `&[T]` and `&mut [T]`.

However, Rust still differs from the C version: `&[T]` is a _fat pointer_, being two words wide.
It essentially looks like this:
```rust
struct Slice {
  len: usize,
  values: *const T,
}
```
A reference to a slice otherwise works like an array reference: `&x[n]` extracts a reference to the `n`th element in the slice (with bounds checking), `x[n] = y` assigns to it.
The length of a slice can also be extracted with the `len` method: `x.len()`.

`str`[^71] is a slice-like type that is guaranteed to contain UTF-8 string data.

Slices can be created from arrays and other slices using a "ranged index operation": `&x[a..b]`[^72]`.` This takes the array or slice `x` and creates a slice with the elements from index `a` to index `b` (inclusive of `a`, exclusive of `b`), of length `b - a`.
`&x[a..]` is the suffix starting at `a`, `&x[..b]` is the prefix ending at `b`, and `&x[..]` is the whole slice, useful for converting arrays into slices.
Inclusive ranges are also available, with the syntax `a..=b`.

Slices can be iterated over, using `for` loops:
```rust
let slice: &[u32] = /* ... */;
for x in slice {
  // x is a reference to the nth element in slice.
}
```

If an index is desired, it is possible to iterate over a range directly:
```rust
for i in 0..slice.len() {
  let x = &slice[i];
  // ...
}
```

This can be combined with the `_` pattern to simply repeat an operation `n` times:
```rust
for _ in 0..n {
  // ...
}
```

One important note with slices, as pertains to borrowing, is unique references.
If we have a unique reference to a slice, it's not possible to take unique references to multiple elements at once:
```
let slice: &mut [u32] = /* ... */;
let x = &mut slice[0];
let y = &mut slice[1];  // Error: slice is already borrowed.
```
The method `split_at_mut()`[^73] can be used to split a unique slice reference into two non-overlapping unique slice references:
```rust
let slice: &mut [u32] = /* ... */;
let (slice1, slice2) = slice.split_at_mut(1);
let x = &mut slice1[0];  // slice[0]
let y = &mut slice2[0];  // slice[1]
```
It is usually possible to structure code in such a way that avoids it, but this escape hatch exists for when necessary.
Slices can also be decomposed into their pointer and length parts, using the `as_ptr()` and `len()` functions, and reassembled with `std::slice::from_raw_parts()`[^74].
This operation is unsafe, but useful for bridging C and Rust, or Rust and Rust across a syscall or IPC boundary.

More slice operations can be found at [https://doc.rust-lang.org/std/slice/index.html](https://doc.rust-lang.org/std/slice/index.html) and [https://doc.rust-lang.org/std/primitive.slice.html](https://doc.rust-lang.org/std/primitive.slice.html).


#### String Literals {#string-literals}

Rust string literals are much like C string literals: `"abcd..."`.
Arbitrary ASCII-range bytes can be inserted with `\xNN`, and supports most of the usual escape sequences.
However, all Rust strings are UTF-8 encoded byte slices: `&str` is a wrapper type around `&[u8]` that guarantees that the bytes inside are valid UTF-8.
The type of all string literals is `&'static str`.

Rust string literals can contain arbitrary newlines in them, which can be escaped:
```rust
// Equivalent to "foo\n  bar".
let s = "foo
  bar";
// Equivalent to "foo  bar".
let s = "foo\
  bar";
```

Raw strings disable escape sequences, and are delimited by an arbitrary, matching number of pound signs:
```rust
let s = r"...";
let s = r#" ..."#;
let s = r#####"..."#####;
```
If instead a byte string with no encoding is required, byte strings can be used: `b"..."`.
Their contents must be ASCII (or escaped bytes), and their type is `&[u8]`.
Raw strings can also be byte strings: `br#"..."#`.

Rust also has character literals in the form of `'z'`[^75], though their type is `char`, a 32-bit Unicode code-point.
To get an ASCII byte of type `u8`, instead, use `b'z'`.

### Destructors and RAII {#destructors-and-raii}

Destructors are special functions that perform cleanup logic when a value has become unreachable (i.e., both the `let` that originally declared it can no longer be named, and the last reference to it expired).
After the destructor is run, each of the value's fields, if it's a struct or enum, are also destroyed (or "dropped").

Destructors are declared with a special kind of `impl` block (we'll see more like this, later):
```rust
impl Drop for MyType {
  fn drop(&mut self) {
    // Dtor code.
  }
}
```
If several values go out of scope simultaneously, they are dropped in reverse order of declaration.

The `drop` method can't be called manually; however, the standard library function `std::mem::drop()` [^76] can be used to give up ownership of a value and immediately destroy it.
Unions[^77] and types with copy semantics cannot have destructors.

Destructors enable the _resource acquisition is initialization_ (RAII) idiom.
A type that holds some kind of temporary resource, like a handle to a peripheral, can have a destructor to automatically free that resource.
The resource is cleaned up as soon as the handle goes out of scope.

The classic example of RAII is dynamic memory management: you allocate memory with `malloc`, stash the returned pointer in a struct, and then that struct's destructor calls `free` on that pointer.
Since the struct has gone out of scope when `free` is called, UAF is impossible.
Thanks to Rust's move semantics, this struct can't be duplicated, so the destructor can't be called twice.
Thus, double-free is also impossible[^78].

In some situations, calling a destructor might be undesirable (for example, during certain Unsafe Rust operations).
The standard library provides the special function `std::mem::forget()`[^79], which consumes a value without calling its destructor.
The `std::mem::ManuallyDrop<T>`[^80] type is a smart pointer[^81] that holds a `T`, while inhibiting its destructor.
For this reason, there is no expectation that a destructor actually runs.

The function `std::mem::needs_drop()`[^82] can be used to discover if a type needs to be dropped; even if it doesn't have a `drop` method, it may recursively have a field which does.
`std::ptr::drop_in_place()`[^83] can be used to run the destructor in the value behind a raw pointer, without technically giving up access to it.


### Pattern Matching {#pattern-matching}

References cannot be null, but it turns out that a null value is sometimes useful.
`Option<T>` is a standard library type representing a "possibly absent `T`"[^84].
It is implemented as an enum:
```rust
enum Option<T> {
  Some(T),
  None,
}
```

The `<T>` is similar to the lifetime syntax we saw before; it means that `Option<T>` is a _generic type_; we'll dig into those soon.

If we have a value of type `Option<T>` (or, any other enum, really), we can write code conditioned on the value's discriminant using _pattern matching_, which is accessed through the `match` expression:
```rust
let x: Option<u32> = /* ... */;
let y = match x {
  Some(val) => val,  // If `x` is a `Some`, bind the value inside to `val`.
  None => 42,  // If `x` is a `None`, do this instead.
};
```

The key thing pattern matching gives us is the ability to inspect the union within an enum safely: the tag check is enforced by the compiler.

Patterns are like expressions, forming a mini-language.
If expressions build up a value by combining existing values, patterns do the opposite: they build up values by deconstructing values.
In particular, a pattern, applied to an expression, performs the following operations:
*   Checks that the expression's value actually matches that pattern.
    (Note that type-checking doesn't go into this; patterns can't be used for conditioning on the type of an expression.)
*   Optionally binds that expression's value to a name.
*   Optionally recurs into subpatterns.

Here's a few examples of patterns.
Keep in mind the matching, binding, and recurrence properties of each.
In general, patterns look like the value of the expression they match.

*   `_`, an underscore[^85] pattern.
    The match always succeeds, but it throws away the matched value.
    This is the `_` in the equivalent of a `default:` case.
*   `foo`, an identifier pattern.
    This pattern is exactly like `_`, but it binds the matched value to its name.
    This is the `val` in the `Some(val)` above.
    This can also be used by itself as a default case that wants to do something with the matched-on value.
    The binding can be made mutable by writing `Some(mut val)` instead.
*   Any numeric literal, for a literal pattern.
    This match compares the matched value against the literal value, and doesn't match anything.
    These can also be inclusive ranges: `5..=16`[^86].
*   `(pat1, pat2, /* etc */)`, a tuple pattern.
    This match operates on tuple types, and always succeeds: it extracts the individual elements of a tuple, and applies them to the pattern's subpatterns.
    In particular, the `()` pattern matches the unit value `()`.
```rust
let x: (u32, u32) = /* ... */;
match x {
  (5, u) => /* ... */,  // Check that first element is five,
                        // bind the second element to `u`.
  (u, _) => /* ... */,  // Bind the first element to `u`,
                        // discard the second element.
}

let y: (u32, (u32, u32)) = /* ... */;
match y {
  // All patterns can nest arbitrarily, like expressions.
  (42, (u, _)) =>  /* ... */,
  // `..` can be used to match either a head or a tail of tuple.
  (.., u) => /* ... */,
  (u, ..) => /* ... */,
  (..) =>    /* ... */,  // Synonymous with _.
}
```
*   Struct patterns are analogous to tuple patterns.
    For a tuple-like struct, they have the exact same syntax, but start with the name of the struct: `MyTuple(a, b, _)`.
    Regular structs are much more interesting syntax-wise:
```rust
struct MyStruct { a: i32, b: u32 }
match my_struct {
  MyStruct { a, b } => /* ... */,  // Bind the fields `a` and `b` to
                                   // names `a` and `b`, respectively.
  MyStruct { a: foo, b: _ } => /* ... */,  // Bind the field `a` to the name
                                           // `foo`, and discard the field `b`.
  MyStruct { a: -5, .. } => /* ... */  // Check that `a` is -5, and ignore
                                       // other fields.
}
```
*   Enum patterns are probably the most important kind of pattern, and are what we saw in the `match` statement with `Option` above.
    They're very similar to struct patterns, except that instead of always succeeding, they check that the enum discriminant is the one named in the pattern.
```rust
enum MyEnum { A, B{u32), C { a: i32, b: i32 }, }
match my_enum {
  MyEnum::A =>    /* ... */,  // Match for variant `A`.
  MyEnum::B(7) => /* ... */,  // Match for variant `B`, with 7 as the value inside.
  MyEnum::B(x) => /* ... */,  // Match for variant `B`, binding the value inside to
                              // `x`.

  MyEnum::C { a: 7, .. } => /* ... */,  // Match for variant `C`, with 7 as the
                                        // value in `a` and all other fields ignored.

  MyEnum::C { b, .. } => /* ... */,  // Match for variant `C`, binding b to b.
}
```
A complete treatment of the pattern syntax can be found at [https://doc.rust-lang.org/book/ch18-03-pattern-syntax.html](https://doc.rust-lang.org/book/ch18-03-pattern-syntax.html).

A `match` expression will evaluate each pattern against a value until one matches, in order; the compiler will warn about patterns which are unreachable[^87].
The compiler will also ensure that every value will get matched with one of the match arms, either because every case is covered (e.g., every enum variant is present) or an _irrefutable pattern_ is present (i.e., a pattern which matches all values). `_`, `foo`, `(a, _)`, and `MyStruct { a, .. }` are all examples of irrefutable patterns.

If the value being matched on is a reference of some kind, bound names will be references, too.

For example:
```rust
match &my_struct {
  MyStruct { a, .. } => {
    // Here, `a` is a `&i32`, which is a reference to the `a` field in my_struct.
  },
}
```
This feature is sometimes called _match ergonomics_, since before it was added, explicit dereference and special `ref` pattern qualifiers had to be added to matches on references.

In addition, `match` statements support two additional features on top of the pattern syntax discussed above:
*   _Multi-match arms_ can allow a match arm to match on one of multiple patterns: `a | b | c => /* ... */,`.
    If any of the patterns match, the arm executes.
*   _Match guards_ give you a shorthand for conditioning an arm on some expression: `Some(foo) if foo.has_condition() => /* ... */,`.

Also, the standard library provides the `matches!()` macro as a shorthand for the following common match expression:
```rust
match expr {
  <some_complex_match_arm> => true,
  _ => false,
}
// ... can be replaced with ...
matches!(expr, some_complex_match_arm)
```
`matches!` supports multi-match and match guards as well.

Irrefutable patterns can be used with normal variable declaration.
The syntax `let x = /* ... */;` actually uses a pattern: `x` is a pattern.
When we write `let mut x = /* ... */;`, we are using a `mut x` pattern instead.
Other irrefutable patterns can be used there:
```rust
// Destructure a tuple, rather than using clunky `.0` and `.1` field names.
let (a, b) = /* ... */;

// Destructure a struct, to access its fields directly.
let Foo { foo, bar, baz } = /* ... */;

// Syntactically valid but not allowed: `42` is not an irrefutable pattern.
let 42 = /* ... */;
```

Special variants of `if` and `while` exist to take advantage of patterns, too:
```rust
if let Some(x) = my_option {
  // If the pattern succeeds, the body will be executed, and `x` will be bound
  // to the value inside the Option.
  do_thing(x);
} else {
  // Else block is optional; `x` is undefined here.
  // do_thing(x);  // Error.
}

while let Some(x) = some_func() {
  // Loop terminates once the pattern match fails. Again, `x` is bound
  // to the value inside the Option.
}
```
Unlike normal `let` statements, `if let` and `while let` expressions are meant to be used with refutable patterns.

In general, almost every place where a value is bound can be an irrefutable pattern, such as function parameters and `for` loop variables:
```rust
fn get_first((x, _): (u32, u32)) -> u32 { x }

for (k, v) in my_key_values {
  // ...
}
```

### Traits {#traits}

Traits are Rust's core code-reuse abstraction.
Rust traits are like interfaces in other languages: a list of methods that a type must implement.
Traits themselves, however, are _not_ types.

A very simple trait from the standard library is `Clone`[^88]:
```rust
trait Clone {
  fn clone(&self) -> Self;
}
```

A type satisfying `Clone`'s interface (in Rust parlance, "implements `Clone`") has a `clone` method with the given signature, which returns a duplicate of `self`.
To implement a trait, you use a slightly funny `impl` syntax[^89]:
```rust
impl Clone for MyType {
  fn clone(&self) -> Self { /* implementation */ }
}
```

This gives us a consistent way to spell "I want a duplicate of this value".
The standard library provides traits for a number of similar operations, such as `Default`[^90], for providing a default value, `PartialEq`[^91] and `Eq`, for equality, `PartialOrd`[^92] and `Ord`, for ordering, and `Hash`[^93], for non-cryptographic hashing.

The above traits are special in that they have trivial implementations for a struct or enum, assuming that all fields of that struct or enum implement it.
The `#[derive()]` syntax described in the "Ownership" section can be used with any of these traits to automatically implement them for a type.
It is not uncommon for Plain Old Data (POD) types to look like this:
```rust
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct MyPod {
  pub a: u8,
  pub b: u8,
  // The following line wouldn't compile, because `derive(Eq)` requires
  // all fields to be `Eq`.
  // c: NonEq,
}
```

Traits can also provide built-in methods implemented in terms of other methods, to provide a default implementation (which can be overridden if a more efficient one is available for a particular type).
The full `Clone` trait actually looks like this:
```rust
pub trait Clone {
  fn clone(&self) -> Self;
  fn clone_from(&mut self, source: &Self) {
    *self = source.clone();
  }
}
```

Implementers don't need to provide `clone_from`, but are allowed to do so if the default implementation isn't good enough.

Traits, and types that implement them, can be defined in different modules, so long as the implementing module defines either the trait or the type.
This means that trait methods aren't really part of the type, but rather part of the trait plus the type.
Thus, in order to call trait methods on a particular type, that trait has to be in scope, too.
When unambiguous, trait functions can be called as either `foo.trait_fn()`, `Foo::trait_fn(foo)`, or `Trait::trait_fn(foo)`.
However, since names can sometimes be ambiguous, there is a fully unambiguous syntax[^94]: `<Foo as Trait>::trait_fn(foo)`.
This last syntax is also useful in generic contexts, or for being precise about the exact function being referred to.

Traits are also the vehicle for operator overloading: these traits are found in the std::ops[^95] module of the standard library.


#### Trait Objects {#trait-objects}

Traits can be used for dynamic dispatch (also known as virtual polymorphism) through a mechanism called _trait objects_.
Given a trait `Trait`, and a type `T` that implements it, we can `as`-cast a reference `&T` into a dynamic trait object: `&dyn Trait`.
For example:
```rust
trait Id {
    fn get_id(&self) -> usize;
}
impl Id for Device {
  // ...
}

let device: Device = /* ... */;
let dyn_id = &device as &dyn Id;  // Create a vtable.
let id = dyn_id.get_id();  // Indirect procedure call.
```

`dyn Trait` is a dynamically-sized type, much like slices, and can only exist behind a pointer.
The reference `&dyn Trait` looks something like this:
```rust
struct TraitObject {
  value: *mut (),
  vtable: *mut Vtable,
}

struct Vtable {
  size: usize,
  align: usize,
  dtor: fn(&mut T),
  // Other trait methods.
}
```
Thus, the dynamic function call to `get_id` would compile to something like the following:
```rust
let device: Device = /* ... */;
let dyn_id = &device as IdTraitObject;
let id = (dyn_id.vtable.get_id)(dyn_id.value);
```

There are some limitations on what traits can be made into trait objects: namely, functions cannot take or return functions of type `Self`; only `&Self` or `&mut Self`[^96].
In other words, all of the functions must treat `Self` as if it were not sized and only accessible through a pointer.[^97] A trait that can be made into a trait object is called _object safe_.
The type `dyn Trait` always behaves as if it implemented `Trait`, which is relevant for generics, discussed below.


#### Unsafe Traits {#unsafe-traits}

It is possible to mark a trait as `unsafe` by writing `unsafe trait MyTrait { /* ... */ }`; the only difference with normal traits is that it requires `unsafe impl` to be implemented.
Unsafe traits typically enforce some kind of additional constraint in addition to their methods; in fact, unsafe traits frequently don't have methods at all.
For example, the standard library trait `Sync` is implemented by all types which synchronize access[^98].
Because the invariant this trait asserts is beyond what the compiler can check, it is an unsafe trait.

Trait methods may separately be marked as `unsafe`.
This is usually done to indicate that not only does care need to be taken in implementing the trait, but calling the function also requires care (and uttering `unsafe`).
This is separate from marking a trait as `unsafe`, and it is not necessary to mark a trait as `unsafe` for it to have `unsafe` methods.


#### Auto Traits

Auto traits are a compiler mechanism for automatically implementing certain traits; in the standard library's source code, this shows up as `auto trait Foo {}` (though this syntax is unavailable for normal libraries).
Auto traits are implemented automatically for a struct or enum type if all of its fields also implement that trait, and are used for exposing transitive properties to the trait system.
For example, `Send` and `Sync` are auto traits; a number of other marker traits[^99] are also auto traits.

Auto traits are always markers that you don't really want to opt out of.
They're like the opposite of `derive()` traits, which you need to opt into, since they meaningfully affect the API of your type in a way that it is important to be able to control.


### Generics {#generics}

_Generic programming_ is writing source code that can be compiled for many types.
Generics are one of Rust's core features, which enable polymorphic[^100] static dispatch.

Functions can be made generic by introducing _type parameters_, using a syntax similar to explicit lifetimes[^101]:
```rust
fn identity<T>(x: T) -> T {
  x
}
```
This function accepts a value of any type and immediately returns it.
It can then be called like this: `identity::<i32>(42)`[^102].
Using a generic function with all of its type parameters filled in causes it to be _instantiated_ (or _monomorphized_), resulting in code being generated for it.
This process essentially consists of replacing each occurrence of `T` with its concrete value.

Each distinct instantiation is a separate function at runtime, with a separate address, though for functions which generate identical code, like `identity::<i32>` and `identity::<u32>`, the linker may deduplicate them.
Overzealous use of generic code can lead to binary bloat.

Most of the time, the `::<>` bit (referred to by some reference materials as the "turbofish") is unnecessary, since Rust type deduction can infer it: `let x: u64 = identity(42);` will infer that `T = u64`.
It can, however, be useful to include when otherwise unnecessary to help with readability.

Types can also be generic, like the  `Option<T>` type from before[^103]:
```rust
struct MyWrapper<T> {
  foo: usize,
  bar: T,
}
```
The concrete type `MyWrapper<i32>` consists of replacing all occurrences of `T` in the definition with `i32`, which we can otherwise use as a normal type:
```
fn get_foo(mw: MyWrapper<i32>) -> usize {
  mw.foo
}
```
Note that `MyWrapper` on its own is not a type.

Note that different generic instantiations are different types, with different layouts and sizes, which cannot be converted between each other in general.[^104]

Unsurprisingly, we can combine generic functions with generic types.
In this case, we don't really need to know that `T = i32`, so we factor it out.
```rust
fn get_foo<T>(mw: MyWrapper<T>) -> usize {
  mw.foo
}
```
We can also build a generic function to extract the generic field:
```rust
fn get_bar<T>(mw: MyWrapper<T>) -> T {
  mw.bar
}
```

Just like with lifetimes, `impl` blocks need to introduce type parameters before they are used:
```rust
impl<T> MyWrapper<T> {
  // ...
}
```


#### Generic Bounds {#generic-bounds}

However, generics alone have one limitation: the function is only type and borrow checked once, in its generic form, rather than per instantiation; this means that generic code can't just call inherent methods of `T` and expect the lookup to succeed[^105].
For example, this code won't compile:
```rust
fn generic_add<T>(x: T, y: T) -> T {
  x + y
}
```

The error looks like this:
```rust
error[E0369]: cannot add `T` to `T`
 --> src/lib.rs:2:6
  |
2 |     x+y
  |     -^- T
  |     |
  |     T
  |
  = note: T might need a bound for std::ops::Add
```
The compiler helpfully suggests that we need a "bound" of some sort.
Generic bounds are where traits really shine.

`Add` is a standard library trait, that looks something like the following:
```rust
trait Add<Rhs> {
  type Output;
  fn add(self, other: Rhs) -> Self::Output;
}
```
Not only is this trait generic, but it also defines an _associated type_, which allows implementations to choose the return type of the addition operation[^106].
Thus, for any types `T` and `U`, we can add them together if `T` implements `Add<U>`; the return type of the operation is the type `<T as Add<U>>::Output`[^107].

Thus, our `generic_add` function should be rewritten into
```rust
fn generic_add<T: Add<T>>(x: T, y: T) -> T::Output {
  x + y
}
```
The `T: Add<T>` part is a generic bound, asserting that this function can only compile when the chosen `T` implements `Add<T>`.

If we want to ensure we return a T, we can change the bound to require that `Output` be `T`:
```rust
fn generic_add<T>(x: T, y: T) -> T
  where T: Add<T, Output=T>
{
  // ...
}
```
Note that this bound is included in a `where` clause, after the return type.
This is identical to placing it in the angle brackets, but is recommended for complicated bounds to keep them out of the way.
In-bracket bounds and `where` clauses are available for all other items that can have generic bounds, such as traits, impls, structs, and enums[^108].

Bound generics can be used to emulate all kinds of other behavior.
For example, the `From` and `Into` traits represent lossless conversions, so a function that wants any value that can be converted into `MyType` might look like
```rust
fn foo<T: Into<MyType>>(x: T) {
  // ...
}
```
You could then implement `From<T>` on `MyType` for all `T` that can be converted into `MyType`.
When `U` implements `From<T>`, a generic `impl` in the standard library causes `T` to implement `Into<U>`.
At the call-site, this looks like an overloaded function[^109].

Bound generics can also be used to pass in constants. Imagine that we define a trait like
```rust
trait DriverId {
  const VALUE: u8;
}
```
This trait could then be implemented by various zero-sized types that exist only to be passed in as type parameters:
```rust
struct GpioDriverId;
impl DriverId for GpioDriverId {
  const VALUE: u8 = 0x4a;
}
```
Then, functions that need to accept a constant id for a driver can be written and called like this:
```rust
fn get_device_addr<Id: DriverId>() -> usize {
  // use Id::VALUE somehow ...
}
// ...
get_device_addr::<GpioDriverId>()
```
Types can also be bound by lifetimes.
The bound `T: 'a` says that every reference in `T` is longer than `'a`; this kind of bound will be implicitly inserted whenever a generic `&'a T` is passed around.
Bounds may be combined: `T: Clone + Default` and `T: Clone + 'a` are both valid bounds.
Finally, lifetimes may be bound by other lifetimes: `'a: 'b` means that the lifetime `'a` is longer than `'b`.


#### Phantom Data

The following struct definition is an error in Rust:
```rust
error[E0392]: parameter `T` is never used
 --> src/lib.rs:2:12
  |
2 | struct Foo<T>;
  |            ^ unused parameter
  |
  = help: consider removing `T`, referring to it in a field,
    or using a marker such as `std::marker::PhantomData`
```

Rust requires that all lifetime and type parameters be used, since generating code to call destructors requires knowing if a particular type owns a `T`.
This is not always ideal, since it's sometimes useful to expose a `T` in your type even though you don't own one; we can work around this using the compiler's suggestion: `PhantomData`.
For more information on how to use it, refer to the type documentation[^110] or the relevant Rustonomicon entry[^111].


### Smart Pointers {#smart-pointers}

In Rust, a "smart pointer"[^112] is any type that implements `std::ops::Deref`[^113], the dereference operator[^114].
`Deref` is defined like this:
```rust
trait Deref {
  type Target;
  fn deref(&self) -> &Self::Target;
}
```
Types which implement `Deref` can also implement the mutable variant:
```rust
trait DerefMut: Deref {
  fn deref_mut(&mut self) -> &mut Self::Target;
}
```

Implementing the `Deref` trait gives a type `T` two features:
*   It can be dereferenced: `*x` becomes syntax sugar for `*(x.deref())` or `*(x.deref_mut())`, depending on whether the resulting lvalue is assigned to.
*   It gains auto-deref: if `x.foo` is not a field or method of `T`, then it expands into `x.deref().foo` or `x.deref_mut().foo`, again depending on use.

Furthermore, `deref` and `deref_mut` are called by doing an explicit reborrow: `&*x` and `&mut *x`.

One example of a smart pointer is `ManuallyDrop<T>`.
Even though this type contains a `T` directly (rather than through a reference), it's still called a "smart pointer", because it can be dereferenced to obtain the `T` inside, and methods of `T` can be called on it.
As we will see later, the `RefCell<T>` type also produces smart pointers.
It is not uncommon for generic wrapper types, which restrict access to a value, to be smart pointers.

Note that, because `Target` is an associated type, a type can only dereference to one other type.

While not quite as relevant to smart pointers, the `Index` and `IndexMut` traits are analogous to the `Deref` and `DerefMut` traits, which enable the `x[foo]` subscript syntax.
`Index` looks like this:
```rust
trait Index<Idx> {
  type Output;
  fn index(&self, index: Idx) -> &Self::Output;
}
```

An indexing operation, much like a dereference operation, expands from `x[idx]` into `*(x.index(idx))`.
Note that indexing _can_ be overloaded, and is a useful example of how this overloading through traits can be useful.
For example, `<[u8] as Index<usize>>::Output` is `u8`, while `<[u8] as Index<Range>>::Output` is `[u8]`.
Indexing with a single index produces a single byte, while indexing with a range produces another slice.


### Closures {#closures}

Closures (sometimes called "lambda expressions" in other languages) are function literals that capture some portion of their environment, which can be passed into other functions to customize behavior.

Closures are not mere function pointers, because of this captured state.
The closest analogue to this in C is a function that takes a function pointer and some "context".
For example, the Linux `pthread_create()` function takes a `void* (*start_routine)(void*)` argument and a `void* arg` argument.
`arg` represents state needed by `start_routine` to execute.
In a similar way, Rust closures need extra state to execute, except `arg` becomes part of the `start_routine` value.
Not only that, Rust will synthesize a bespoke context struct for `arg`, where normally the programmer would need to do this manually.
Rust makes this idiom much easier to use, and, as such, much more common.

As we'll see, Rust has a number of different ABIs for closures, some of which closely resemble what `pthread_create` does; in some cases, the function pointer and its context can even be inlined.

In Rust, the syntax for creating a closure is `|arg1, arg2| expr`.
They can be very simple, like `|(k, _)| k` (which uses pattern-matching to extract the first element of a tuple) or complex, using a block expression to create a longer function: `|foo| { /* ... */ }`.
The types of arguments can be optionally specified as `|foo: Foo| { /* ... */ }`, and the return type as `|foo| -> Bar { /* ... */ }`, though in almost all cases type inference can figure them out correctly.
A closure that takes no arguments can be written as `|| /* ... */`.

Closures capture their environment by reference; the mutable-ness of that reference is inferred from use.
For example:
```rust
let x = /* ... */;
let y = /* ... */;
let f = |arg| {
  x.do_thing(arg);  // Takes &self, so this implicitly produces a shared reference.
  y.do_mut_thing(arg);  // Takes &mut self, so it takes a unique reference instead.
};
// Note: f holds a unique borrow of y.
let z = &mut y;  // Error!
```

Above, `f` captures `x` by shared reference and `y` by unique reference.
The actual closure value `f` is a synthetic struct containing the captures:
```rust
struct MyClosure<'a> {
  x: &'a X,
  y: &'a mut Y,
}
```
Calling a closure, like `f()`, calls a synthetic function that takes `MyClosure` as its first argument.
It's possible to instead capture by moving into the closure; this can be done with the `move |arg| { /* ... */ }` syntax.
If it were applied to `f`, `MyClosure` would become
```rust
struct MyClosure<'a> {
  x: X,
  y: Y,
}
```

Rust does not cleanly support mixing capture-by-move and capture-by-reference, but it is possible to mix them by capturing references by move:
```rust
let x = /* ... */;
let y = /* ... */;
let x_ref = &x;
let f = move |arg| {
  x_ref.do_thing(arg);  // Capture x_ref by move, aka capture x by shared ref.
  y.do_mut_thing(arg);  // Capture y by move.
};
```
The distinction between capture-by-move and capture-by-ref is mostly irrelevant for `Copy` types.

To be polymorphic over different closure types, we use the special `Fn`, `FnMut`, and `FnOnce` traits.
These represent functions that can be called by shared reference, unique reference, or by move.
Closures that only capture shared references implement all three; closures that capture by unique reference implement only the latter two, and closures that capture by move implement only the last one[^115].
Function pointers, function items[^116], and closures that don't capture also implement all three, and can all be converted to function pointers.

These traits use special syntax similar to function pointers[^117].
For example, `Fn(i32) -> i32` represents taking an `i32` argument and returning another `i32`.
Closures also implement `Copy` and `Clone` if all of their captures do, too.


#### Closures as Function Arguments {#closures-as-function-arguments}

There are roughly two ways of writing a function that accepts a closure argument: through dynamic dispatch, or through static dispatch, which have a performance and a size penalty, respectively.

`Fn` and `FnMut` closures can be accepted using trait objects:
```rust
fn my_do_thing(func: &dyn Fn(i32) -> i32) -> i32 {
  func(MY_CONST)
}
```
This is completely identical to the C approach: the synthetic function lives in the trait object vtable, while the captures are behind the actual trait object pointer itself.
In other words:
```rust
struct DynClosure {
  vtable: *mut Vtable,
  captures: *mut Captures,
}
```
Of course, the vtable call has a performance penalty, but avoids the code size overhead of generic instantiation.

Using generics allows passing in closures implementing `Fn`, `FnMut`, or `FnOnce`, by specializing the called function for each function type:
```rust
fn my_do_thing<F: Fn(i32) -> i32>(func: F) -> i32 {
  func(MY_CONST)
}
```
This will translate to a direct call to the synthetic closure function with no overhead, but will duplicate the function for each closure passed in, which can result in a big size hit if used on large functions.

It is possible to use a shorthand for declaring this type of function, that avoids having to declare a type parameter:
```rust
fn my_do_thing(func: impl Fn(i32) -> i32) -> i32 { /* ... */ }
```

The pseudotype `impl Trait` can be used in function argument position to say "this parameter can be of any type that implements `Trait`", which effectively declares an anonymous generic parameter.
Note that `Trait` can technically be any generic bound involving at least one trait: `impl Clone + Default` and `impl Clone + 'a` are valid.


#### Closures as Function Returns {#closures-as-function-returns}

Closure types are generally unnameable. The canonical way to return closures is with `impl Trait` in return position:
```rust
fn new_fn() -> impl Fn(i32) -> i32 {
  |x| x * x
}
```

Return-position `impl Trait` means "this function returns some unspecified type that implements `Trait`".
Callers of the function are not able to use the actual type, only functions provided through `Trait`.
`impl Trait` can also be used to hide implementation details, when a returned value only exists to implement some trait.

Return-position `impl Trait` has a major caveat: it cannot return multiple types that implement the trait.
For example, the following code is a type error:
```rust
fn new_fn(flag: bool) -> impl Fn(i32) -> i32 {
  if flag {
    |_| 0
  } else {
    |x| x * x
  }
}
```
The resulting compiler error looks like this:
```rust
  = note: expected type `[closure@src/lib.rs:3:5: 3:10]`
          found closure `[closure@src/lib.rs:5:5: 5:14]`
  = note: no two closures, even if identical, have the same type
  = help: consider boxing your closure and/or using it as a trait object
```
In a non-embedded context, the solution (as suggested by the compiler) would be to allocate the closures on the heap, and use trait objects.
However, allocation is limited in embedded contexts, so this solution is unavailable.

If none of the closures capture, returning a function pointer may be an acceptable solution:
```rust
fn new_fn(flag: bool) -> fn(i32) -> i32 {
  if flag {
    |_| 0
  } else {
    |x| x * x
  }
}
```
#### Closures as Struct Fields {#closures-as-struct-fields}

Using closures as struct fields is fairly limited without being able to easily allocate.
The two options are to either make the trait generic on the closure type (which needs to be propagated through everything that uses the struct), or to require that closures not capture, and use function pointers instead:
```rust
struct MyStruct<F>
  where F: Fn(i32) -> i32 {
  val: usize,
  func: F,
}
// Vs.
struct MyStruct {
  val: usize,
  func: fn(i32) -> i32,
}
```
In general, function pointers are easiest, and the requirement of no captures is not particularly onerous.
The generic variant tends to be more useful for short-lived types, like combinators.

Short-lived structs can also try to use trait objects, but the lifetime requirement can be fairly limiting:
```rust
struct MyStruct<'a> {
  val: usize,
  func: &'a dyn Fn(i32) -> i32,
}
```


### `Option` and `Result`: Error Handling in Rust {#option-and-result-error-handling-in-rust}

As we saw above, `Option` is a type that lets us specify a "potentially uninitialized" value.
While it is common to work with `Option` using `match` expressions, it also has a number of convenience functions that shorten common sequences of code.
`is_none()` can be used to check that an `Option` is empty; `map` can be used to convert the value inside an Option:
```rust
opt.map(|t| t + 1)  // Increments the value inside, if there is one.
```

`unwrap_or()` can be used to extract the value inside, with a default:
```rust
opt.unwrap_or(42)  // Get the value inside, or the value 42 if the former is unavailable.
```

The documentation for `Option` describes a number of other potential uses and operations on `Option`: [https://doc.rust-lang.org/std/option](https://doc.rust-lang.org/std/option/).
The type documentation itself has a full list of all of the convenience functions defined for `Option`: [https://doc.rust-lang.org/std/option/enum.Option.html](https://doc.rust-lang.org/std/option/enum.Option.html).

One key application of `Option` is safe nullable references: `Option<&T>`.
The Rust language guarantees that `Option<&T>` is identical to a nullable pointer at the ABI layer[^118], so it can be safely passed that way into C code.
This optimization is also available for structs which contain at least one reference: the `is_none()` bit will be compressed into one of the struct's reference fields.
Some other types are also eligible for memory layout optimization, such as `NonZeroI32`[^119].

`Result<T, E>` is similar to `Option<T>`, but rather than having an "empty" state, it has an "error" state:
```rust
enum Result<T, E> {
  Ok(T),
  Err(E),
}
```

A `Result<T, E>` represents a completed computation of a value of type `T` that might have gone wrong.
The "gone wrong" part is represented by some user-specified type `E`.
`E` is usually some kind of enum type, since Rust does not have a single error type for all situations.
```rust
enum MyError {
  DeadlineExceeded,
  BufferExhausted(usize),
  OtherError(ErrorCode),
}
```
It is fairly common to define custom `Result` types using a common error enum for your code:
```rust
type Result<T> = std::result::Result<T, MyError>;
```

In a way, `Option<T>` is just a `Result<T, ()>`, where the error type is just the trivial unit tuple.
Rust provides a number of functions for converting between them:
```rust
opt.ok_or(error)  // Converts Option<T> into Result<T, E>, using the provided error if
// the Option is empty.
res.ok()  // Discards the error portion and returns an Option<T>.
res.err()  // Discards the ok portion and returns an Option<E>.
```
Computations that are executed for their side-effects which can fail, such as a write, tend to return `Result<(), E>`.
This is unlike `C`, where the handling of functions that can fail is inconsistent when they return `void`, because `void` is not a real type.

Sometimes, it is necessary to produce a `Result`, due to some trait's interface, for an operation that cannot fail.
Current practice is to use the type `Result<T, std::convert::Infallible>`[^120], which can be matched on as follows:
```rust
let res: Result<T, Infallible> = /* ... */;
match res {
  Ok(t) => { /* ... */ },
  Err(x) => match x {},
}
```
See [https://doc.rust-lang.org/std/convert/enum.Infallible.html](https://doc.rust-lang.org/std/convert/enum.Infallible.html) for more information.

`Result` supports a special early-return syntax.
When in a function returning `Result<T, E>`, and you have a value `res` of type `Result<U, E>`, the expression `res?` will unwrap the `Result`, and get the "ok" value inside if it's present, or immediately return with the error if it isn't.
That is, `res?` is translated to
```result
match res {
  Ok(x) => x,
  Err(e) => return Err(e),
}
```
This question mark operator can be chained with methods, so that straightforward code that early-returns on the first error can be written without explicit control flow:
```
let x = my_thing.foo()?.bar()?.baz()?;
```
See [https://doc.rust-lang.org/std/result/index.html](https://doc.rust-lang.org/std/result/index.html) for more `Result` operations.


### `for` Revisited: Iterators {#for-revisited-iterators}

An _iterator_ is any type that implements the `Iterator` trait, which looks like this:
```rust
trait Iterator {
  type Item;
  fn next(&mut self) -> Option<Self::Item>;
}
```

An iterator produces a sequence of `Option<Item>` values; the `next()` method allows an iterator to advance some internal state and produce the next value in the sequence.

For example, a very simple iterator simply produces every nonnegative integer value, in sequence:
```rust
struct Counter { state: u64 }
impl Iterator for Counter {
  type Item = u64;
  fn next(&mut self) -> Option<u64> {
    let current = self.state;
    self.state += 1;
    Some(current)
  }
}
```

This iterator will produce values forever: it always returns `Some`.
An iterator that eventually produces `None`, and then forever more returns `None`, is called "fused"[^121].
Some iterators may start returning `Some` again after returning `None`, but most Rust constructs treat all iterators as if they are fused.

A related trait is the `IntoIter` trait:

```rust
trait IntoIter {
  type Iter: Iterator;
  fn into_iter(self) -> Self::Iter;
}
```

An `IntoIter` type can be converted into an iterator.
This type is used to drive the `for` loops we saw for iterating slices:
```rust
for pattern in expr {
  // ...
}
// is syntactic sugar for
let iter = expr.into_iter();
while let Some(pattern) = iter.next() {
  // ...
}
```
In the slice example, `&'a [T]` implements `IntoIter`, which produces an iterator that produces each element of the slice, in sequence; the `Range<i32>` type (which is what the syntax `0..32` produces) also implements `IntoIter`.

All this machinery allows users to build their own iterators for use with `for` loops for their own types, or using existing iterators and _iterator combinators_.
The `Iterator` trait defines dozens of provided methods, which can be used to build more complex iterators.
Here are a few examples of particularly useful combinators:

*   `iter.chain(iter2)`.
    Chains two iterators with the same `Item` type together.
     The second iterator starts one `iter` produces `None`.
*   `iter.peekable()`.
    Converts the iterator into an iterator with a `.peek()` function, which returns a reference to the next value in the sequence (but does not advance it).
*   `iter.enumerate()`.
    Changes the `Item` type from `T` into `(usize, T)`, tracking the current index in the sequence along with the value.
*   `iter.step_by(n)`.
    Changes the iterator to return every `n`th element.
*   `iter.take(n)`.
    Shortens the iterator to return `n` elements before fusing.
*   `iter.map(|x| /* ... */)`.
     Applies a closure to each element lazily.
*   `iter.filter(|x| /* ... */)`.
     Applies a predicate to each element; if the predicate returns `false`, it is skipped by `next()`.

A number of other traits can enhance the properties of an iterator, enabling further methods: `ExactSizeIterator` iterators produce a known, fixed number of values; `DoubleEndedIterators` can have elements pulled from both the front, and the back of the sequence.
While many of the operations above have naive implementations in terms of `next`, standard library iterators will override them when a more efficient algorithm is available.
In general, iterators can produce very efficient code similar to that emitted by `while` loops, but care should be taken when using especially complex chains of combinators.

See [https://doc.rust-lang.org/std/iter/trait.Iterator.html](https://doc.rust-lang.org/std/iter/trait.Iterator.html) and [https://doc.rust-lang.org/std/iter](https://doc.rust-lang.org/std/iter/) for full details on available operations.


### Modules and Crate Layout {#modules-and-crate-layout}

Each Rust crate is (from the compiler's perspective) given a unique, single-identifier name.
This name is used to namespace a crate's symbols[^122].
`core` and `std` are crates.

Each crate is rooted at a `lib.rs` or `main.rs` file, depending on whether it is a library or a binary.
This file can declare _modules_, which are sub-namespaces of a crate:
```rust
// Declares a public module named `devices`. Its definition is found in
// either `devices.rs` or `devices/mod.rs`, relative to the current file.
pub mod devices;

// Declares a private module named `tests`. Its definition is found
// within the curly braces.
mod tests {
  // ...
}

// Declares a private module named `generated`. Its definition is found
// in the given path.
#[path = "relative/path/to/file.rs"]
mod generated;
```
Modules can nest arbitrarily: a module can declare more modules.

Symbols in a module can be referred to by paths: `std::mem::drop` refers to the symbol `drop` in the module `std::mem` of crate `std`.
`crate::devices::gpio::Gpio` refers to the symbol `Gpio` in the module `devices::gpio` of the current crate.

`use` items can be used to create symbol aliases in the current scope:
```rust
// Pull in std::mem::drop, aliased to `drop`.
use std::mem::drop;

// Pull in the module std::mem, so we can now write `mem::drop` for `std::mem::drop`.
use std::mem;

// Pull in both size_of and drop:
use std::mem::{size_of, drop};

// Pull in all symbols in `std::mem`, including `drop`. Should typically be best
// avoided, for readability.
use std::mem::*;

// Pull in all symbols from the parent module:
use super::*;

// Pull in a symbol from a submodule (synonymous with using the full
// path starting with `crate`).
use self::devices::Gpio;

// Pull in a name, but rename it.
use std::io::Result as IoResult;

// Pull in a trait to enable its methods, but without pulling its name
// into scope.
use std::io::Write as _;
```

Note that this is subject to visibility restrictions.
By default, all symbols are "private", only visible in the current module and its child modules.
This can be spelled explicitly as `pub(self)`.
A symbol can be restricted to the parent module and child modules with `pub(super)`, and to the current crate with `pub(crate)`.
Finally, a symbol can be restricted to a particular path using `pub(in that::path)`.
`pub` simply means "public everywhere".

Pretty much all items can be marked with visibilities, except `impl`s.
Marking a module with visibility restricts the visibility of all items within.
A `pub` symbol in a `pub(crate)` module is `pub(crate)`.
`use` statements can also be marked with visibility: this will cause the imported symbols to become part of the module.
For example, `std` is full of instances of `pub use core::Symbol;`, to enable `core` symbols to be imported through `std`.

Even `use` items can be marked with visibility:
```rust
// mod my_mod
pub use std::mem::size_of;
```
This means that other modules can now access the symbol `size_of` through `my_mod::size_of`, effectively re-exporting the symbol.
This is how many fundamental `core` types are accessible through the `std` crate as well.

Rust does not have headers, or declaration order constraints; modules within a crate can freely form cyclic dependencies, since they are not units of compilation, merely namespaces.
Rust crate namespaces are closed: after a crate is fully compiled, no other symbols can be added to it.


### Interior Mutability {#interior-mutability}

_Interior mutability_ is a borrow check escape hatch for working around Rust's aliasing rules.

Normally, Rust requires that you prove statically that you have unique access to a value before you mutate it.
`UnsafeCell<T>`[^123] is a special, compiler-blessed[^124] type which contains a single `T`, and has a method `fn get(&self) -> *mut T`.
When you can guarantee at runtime that a shared reference to an `UnsafeCell` is actually unique, the raw pointer returned by `get()` can be converted into a unique reference.
This makes it possible to safely mutate code that is known, at runtime, to be uniquely owned.
Of course, it is very unsafe to use `UnsafeCell` directly, and exists to form the basis of other abstractions.

There are two common strategies for exposing interior mutability safely: the `Cell`[^125] approach and the `RefCell`[^126] approach.

The `Cell` approach simply never creates a unique reference at all: instead, it holds a valid `T` at all times, and provides a `swap` primitive for taking out the `T` and leaving behind another one.
This way, no aliasing rules need to be enforced, since no reference actually points to that `T`.

The `RefCell` approach instead does basic borrow checking at runtime.
In addition to holding a `T`, a `RefCell` holds a counter of the number of outstanding shared references (or a sentinel value for an outstanding unique reference).
The `try_borrow()` and `try_borrow_mut()` methods dynamically check if such a borrow is valid (no outstanding unique references, or no outstanding references at all, respectively), and return a `Result` to indicate success or failure.
On success, the returned value is a smart pointer wrapping a reference, whose destructor will decrement the shared/unique reference count in the original `RefCell`.
In other words, a `RefCell` is like a single-threaded read-write mutex, without the cost of atomicity.

Other abstractions can be built on top of `UnsafeCell` that maintain the aliasing invariants with other strategies, but they will ultimately be analogous to one of `Cell` or `RefCell`.

Interior mutability is also one of the main differences between a constant and a static:
```rust
static S: MyCell<u32> = MyCell::new(0);
const C: MyCell<u32> = MyCell::new(0);

S.set(1);
S.get();  // value = 1, because `set` modified the memory location.
C.set(1);
C.get()  // value = 0, because `set` modified an inlined copy.
```
Note that the memory behind `S` changed, so it must be allocated in a `.data` or `.bss` section.
This illustrates another property of `UnsafeCell`: it causes data that is otherwise declared as immutable to be allocated as mutable.

See [https://doc.rust-lang.org/std/cell/index.html](https://doc.rust-lang.org/std/cell/index.html) for more details; as with all aliasing-related topics, it requires careful attention t detail, and this section is far from exhaustive.


### Unsafe Rust {#unsafe-rust}

Unsafe Rust is a dialect of Rust that is denoted by the keyword `unsafe`: `unsafe` blocks, unsafe functions, unsafe traits.
Importantly, all of these actions require uttering the keyword `unsafe`, so that they can be easily detected in code review.
Code inside unsafe blocks says to the  reader that the programmer has checked subtle safety guarantees that the compiler cannot on its own.

Unsafe Rust fundamentally works by "turning off" certain checks the compiler normally enforces, whenever inside a `unsafe { /* ... */ }` block expression or the body of an `unsafe fn`.
The things that Unsafe Rust can do that Safe Rust cannot are:
*   Call `unsafe` functions.
*   Dereference raw pointers.
*   Mutate global state through a mutable `static`.
*   Read union fields.
*   Call the `asm!` macro.

Additionally, `unsafe impl`s may implement `unsafe trait`s, but don't need to be inside an `unsafe` block.

The canonical reference is the Rustonomicon[^127], a non-normative document describing common uses for Unsafe Rust.
It is required reading (mostly the first half) for embedded programming.
It contains detailed examples of correct and incorrect Unsafe Rust usage, and guidance on when to invoke Unsafe Rust.

Throughout this document, references to Unsafe Rust are made, mostly around calling unsafe functions and referencing raw pointers, which are roughly all that Unsafe Rust can do that normal Rust can't.
With these powers comes responsibility: Unsafe Rust is not safe from Undefined Behavior, and cannot leave the machine in a state where actions allowed in normal, safe Rust would trigger Undefined Behavior.
In general, a few rules of thumb are useful:
*   Every `unsafe fn` should declare, in documentation, what invariants it assumes that the caller will uphold, and what state it will leave the machine in.
    For example, `<[T]>::get_unchecked(n)` elides the bounds check for the indexing operation, and it is up to the caller to uphold it instead.
*   Every time `unsafe` code calls into a non-`unsafe` function, it must ensure that no violated invariants, which could trigger Undefined Behavior, are observable in that safe code.
    For example, if we have a type that maintains the invariant that `len > 0`, and we temporarily set it to `0` during an `unsafe` block, it must be restored to `> 0` before any safe methods can be called on that type[^128].
*   Unsafe code should be kept to the absolute minimum, and wrapped in safe interfaces that assert invariants, either through static type-system guarantees or through runtime checks.
    Every line of unsafe code is a place where the engineering cost of Rust's guarantees are wasted.

In other words, Safe Rust is able to freely assume that Rust's guarantees on aliasing, ownership, and representation of values hold at all times.
This assumption is pervasive: not only does the compiler use it aggressively optimize code for speed and size, but other library code, such as the destructors of wrapper types, assume it, too.
Unsafe Rust is responsible for upholding this core guarantee.
In a way, Unsafe Rust is responsible for protecting Safe Rust.

## Footnotes

[^1]: The "embedded Rust book" is a useful resource for existing rust programmers.
This document assumes no knowledge of Rust or C++.

[^2]: In particular, use-after-frees, double frees, null dereferences, and data races are all impossible in Rust without using the keyword `unsafe`; this applies for most other things traditionally considered Undefined Behavior in C.
However, Unsafe Rust has Undefined Behavior, and, due to its stronger invariants, Rust is generally more punishing than C compilers when Undefined Behavior occurs.

[^3]: Alternative implementations exist, though `rustc` is the reference implementation.
Rust is still in the process of being specified, so, for now, `rustc`'s behavior is mostly normative.

[^4]: Not every project uses rustup, but it's frequently necessary for "nightly" features.

[^5]: Inline assembly is the most salient of these.
Nightly also provides support for the sanitizers, such as ASAN and TSAN.

[^6]: Example from Tock: [https://github.com/tock/tock/blob/master/rust-toolchain](https://github.com/tock/tock/blob/master/rust-toolchain)

[^7]: Rust libraries use their own special "rlib" format, which carries extra metadata past what a normal .a file would.

[^8]: While each crate is essentially a giant object file, Rust will split up large crates into smaller translation units to aid compilation time.

[^9]: The formatter is kind of a new component, so may require separate installation through `rustup`.
See [https://github.com/rust-lang/rustfmt#on-the-stable-toolchain](https://github.com/rust-lang/rustfmt#on-the-stable-toolchain).

[^10]: [https://doc.rust-lang.org/core/index.html](https://doc.rust-lang.org/core/index.html)

[^11]: They are also used analogously to `ptrdiff_t` and `size_t`.
In practice, these types are all the same width on modern systems, though C draws a distinction for portability reasons.

[^12]: Note that Rust spells bitwise negation on integers as `!x` rather than `~x`.
This is because Rust has a separate boolean type, for which `!x` is logical not.

[^13]: Rust has slightly less absurd precedence rules around bitwise operators; `x ^ y == z` is `(x ^ y) == z`.

[^14]: In C, signed overflow is UB, and unsigned overflow always wraps around.

[^15]: Really, this causes a "panic", which triggers unwinding of the stack.
In embedded contexts, unwinding is disabled, so this is just a jump to the panic handler, which performs a platform-specific abort.

[^16]: rustc performs the former in debug builds and the latter in release builds.

[^17]: Creating `bool`s with any other representation, using Unsafe Rust, is instant UB.
This is sometimes called the "validity invariant", and applies to other restricted-range types, such as padding bytes in structs.
["What The Hardware Does" is not What Your Program Does: Uninitialized Memory](https://www.ralfj.de/blog/2019/07/14/uninit.html) provides a short explanation about why this is important.

[^18]: These functions are frequently entry-points for LLVM intrinsics, similar to GCC/Clangs `__builtin_clz()` and similar.

[^19]: This syntax: `(my_struct_t) { .a = 0, .b = 1 }`.

[^20]: Rust allows trailing commas basically everywhere.

[^21]: Currently, the compiler will reorder struct fields to minimize alignment padding, though there is ongoing discussion to add a "struct field layout randomization" flag as an ASLR-like hardening.

[^22]: It has some issues, similar to the C variant.
See [https://doc.rust-lang.org/nomicon/other-reprs.html#reprpacked](https://doc.rust-lang.org/nomicon/other-reprs.html#reprpacked)

[^23]: Unlike C, Rust has true zero-sized types (ZSTs).
They are completely elided from the program at runtime, but can be useful for creating abstractions.

[^24]: This is similar to how a `bool` must always be `0` or `1`.
One could even imagine that `bool` is defined as `enum bool { false = 0, true = 1 }`.

[^25]: Without uttering `unsafe`, it is impossible to witness uninitialized or invalid data.
Doing so even with `unsafe` is Undefined Behavior.

[^26]: This feature is also sometimes known as "algebraic data types".

[^27]: This syntax requires that the array component type be "copyable", which we will get to later.

[^28]: These accesses are often elided.
LLVM is very good at optimizing them away, but not perfect.

[^29]: In C, pointers must _always_ be well-aligned.
Rust only requires this when dereferencing the pointer.

[^30]: In other words, Rust's aliasing model for pointers is the same as that of `-fno-strict-aliasing`.
Rust allows `*mut u32` and `*mut u64`to alias, for example.

[^31]: In C, it is technically UB to forge raw pointers (such as creating a pointer to an MMIO register) and then dereference them, although all embedded programs need to do this anyway.
While Rust has not yet formalized what this means, it seems unlikely that they will make forging raw pointers to MMIO regions UB.

[^32]: Or by casting zero.

[^33]: Rust currently does not have an equivalent of the `->` operator, though it may get one some day.
As such, it is not possible to get pointers to fields of a pointer-to-struct without creating a reference along the way.

[^34]: We will get into references later.

[^35]: We will learn more about "move semantics" when we discuss ownership.

[^36]: However, great care should be taken when using these methods on types that track ownership of a resource, since this can result in a double-free when the pointee is freed.

[^37]: [https://doc.rust-lang.org/std/primitive.pointer.html#method.read_unaligned](https://doc.rust-lang.org/std/primitive.pointer.html#method.read_unaligned)

[^38]: [https://doc.rust-lang.org/std/primitive.pointer.html#method.write_unaligned](https://doc.rust-lang.org/std/primitive.pointer.html#method.write_unaligned)

[^39]: These are effectively memcpys: they will behave as if they read each byte individually with no respect for alignment.

[^40]: [https://doc.rust-lang.org/std/primitive.pointer.html#method.copy_to](https://doc.rust-lang.org/std/primitive.pointer.html#method.copy_to)

[^41]: [https://doc.rust-lang.org/std/primitive.pointer.html#method.copy_to_nonoverlapping](https://doc.rust-lang.org/std/primitive.pointer.html#method.copy_to_nonoverlapping)

[^42]: Rust also provides an abstraction for dealing with uninitialized memory that has somewhat fewer sharp edges: [https://doc.rust-lang.org/std/mem/union.MaybeUninit.html](https://doc.rust-lang.org/std/mem/union.MaybeUninit.html).

[^43]: Rust also allows taking the addresses of rvalues, which simply shoves them onto `.rodata` or the stack, depending on mutation.
For example, `&0` is valid, and produces an address in `.rodata`, while `&mut 0` will push into the stack. The mechanism that converts `&0` into a reference to a constant is called *rvalue promotion*, since `0`, an rvalue of limited lifetime, is promoted into a constant, which has `'static` lifetime.

[^44]: Completely unrelated to the meaning of this keyword in C, where it specifies a symbol's linkage.

[^45]: Immutable statics seem pretty useless: why not make them constants, since you can't mutate them?
This distinction will arise again when we discuss _interior mutability_ towards the end of the document.
Also, like globals in `C`, these static variables can be made visible to other libraries.

[^46]: In practice, this is just the C calling convention, except that `#[repr(Rust)]` structs and enums are aggressively broken up into words so they can be passed in registers.
On 32-bit RISC-V, `(u64, u32, i32)` is passed in four registers.
Rust functions also do some handling of "panics" in their prologues that is mostly irrelevant in an embedded context.

[^47]: Supported calling conventions: [https://doc.rust-lang.org/nomicon/ffi.html#foreign-calling-conventions](https://doc.rust-lang.org/nomicon/ffi.html#foreign-calling-conventions)

[^48]: For those familiar with C++, extern blocks *do* disable name mangling there.

[^49]: Rust's type inference is very powerful, which is part of its ML heritage.
Readable Rust code should include type annotations where necessary to ensure that the type of every `let` can be deduced without having to look at distant context; this is analogous to similar advice for `auto` in C++.

[^50]: It is also possible to leave off the expression in a `let` binding: `let x;`.
The variable cannot be used until Rust can prove that, in all branches of the program, the variable has been assigned to (and, of course, all the assignments must produce the same type).

[^51]: A missing else block implicitly gets replaced by `else {}`, so the type of all blocks needs to be `()`.

[^52]: The value being matched on is called the "scrutinee" (as in scrutinize) in some compiler errors.

[^53]: Rust has a long-standing miscompilation where `loop {}` triggers UB; this is an issue with LLVM that is actively being worked on, and which in practice is rarely an issue for users.

[^54]: Needless to say, all `break`s must have the same type.

[^55]: Rust's execution model is far more constrained than C, so C function calls are basically black boxes that inhibit optimization.
However, there is no runtime cost compared to cross-library-calls in C.

[^56]: [https://doc.rust-lang.org/std/primitive.pointer.html#method.read_volatile](https://doc.rust-lang.org/std/primitive.pointer.html#method.read_volatile)

[^57]: [https://doc.rust-lang.org/std/primitive.pointer.html#method.write_volatile](https://doc.rust-lang.org/std/primitive.pointer.html#method.write_volatile)

[^58]: Of course, due to an LLVM bug, this is not guaranteed to work...

[^59]: Caveats apply as with `__attribute__((inline_always))`.

[^60]: This coincides with the similar notion in C++: the _owner_ of a value is whomever is responsible for destroying it. We'll cover Rust destructors later on.

[^61]: "Owners" don't need to be stack variables: they can be heap allocations, global variables, function parameters for a function call, or an element of an array.

[^62]: Suggested pronunciations include: "tick a", "apostrophe a", and "lifetime a".

[^63]: These days, it's a subgraph of the control flow graph.

[^64]: The compiler does so using strict "elision rules", and does not actually peek into the function body to do so.

[^65]: Rust is so strict about this that it will mark code as unreachable and emit illegal instructions if it notices that this is happening.

[^66]: Also, note that strict aliasing does not apply to shared references, either.
`&u32` and `&u64` may alias, but `&mut u32` and `&mut u64` cannot, because a `&mut T` can never alias with any other active reference.

[^67]: To put it in perspective, all references are marked as "dereferenceable" at the LLVM layer, which gives them the same optimization semantics as C++ references.
Merely materializing an invalid reference is Undefined Behavior, because LLVM will treat it as a pointer to valid memory that it can cache reads from and combine writes to.

[^68]: It is common convention in Rust to name the default function for creating a new value `new`; it is not a reserved word.

[^69]: Note the capital S.

[^70]: This is currently fairly restricted; for our purposes, only `Self`, `&Self`, and `&mut Self` are allowed.

[^71]: There's only a couple of dynamically sized types built into the language; user-defined DSTs exist, but they're a very advanced topic.

[^72]: https://doc.rust-lang.org/std/str/index.html

[^73]: It should be noted that `a..b` is itself an expression, which creates a `Range<T>` of the chosen numeric type.

[^74]: [https://doc.rust-lang.org/std/primitive.slice.html#method.split_at_mut](https://doc.rust-lang.org/std/primitive.slice.html#method.split_at_mut)

[^75]: [https://doc.rust-lang.org/std/slice/fn.from_raw_parts.html](https://doc.rust-lang.org/std/slice/fn.from_raw_parts.html)

[^76]: The second quote disambiguates them from lifetime names.

[^77]: `Drop` is technically a trait, but it is an extremely fake trait.
In particular, `T: Drop` does *not* determine whether `T` needs to call destructors; `std::mem::needs_drop::<T>()` should be used, instead.

[^78]: [https://doc.rust-lang.org/std/mem/fn.drop.html](https://doc.rust-lang.org/std/mem/fn.drop.html)

[^79]: Unions also cannot contain types with destructors in them.

[^80]: While not available in embedded environments, `Box<T>` in the standard library is an implementation of this idea: [https://doc.rust-lang.org/std/boxed/index.html](https://doc.rust-lang.org/std/boxed/index.html).

[^81]: [https://doc.rust-lang.org/std/mem/fn.forget.html](https://doc.rust-lang.org/std/mem/fn.forget.html)

[^82]: [https://doc.rust-lang.org/std/mem/struct.ManuallyDrop.html](https://doc.rust-lang.org/std/mem/struct.ManuallyDrop.html)

[^83]: We'll get to these later.

[^84]: [https://doc.rust-lang.org/std/mem/fn.needs_drop.html](https://doc.rust-lang.org/std/mem/fn.needs_drop.html)

[^85]:
[https://doc.rust-lang.org/std/ptr/fn.drop_in_place.html](https://doc.rust-lang.org/std/ptr/fn.drop_in_place.html)

[^86]: Though naively, it might seem like this would make `Option<T>` bigger than `T` (twice as big, for an integer type, where alignment == size), the compiler can optimize the size down.
For example, as we'll see later, `Option::<&T>::None` is represented as a null pointer, since `&T` can never be null.

[^87]: The single underscore is a keyword in Rust.

[^88]: Inclusive ranges are currently an unstable feature.

[^89]: Of course, the compiler has no problem optimizing match expressions into C switch statements when possible.

[^90]: [https://doc.rust-lang.org/std/clone/trait.Clone.html](https://doc.rust-lang.org/std/clone/trait.Clone.html)

[^91]: Yes, `Drop` is a trait, but mostly does not behave like one, and merely shares syntax with normal traits.

[^92]: [https://doc.rust-lang.org/std/default/trait.Default.html](https://doc.rust-lang.org/std/default/trait.Default.html)

[^93]: [https://doc.rust-lang.org/std/cmp/trait.PartialEq.html](https://doc.rust-lang.org/std/cmp/trait.PartialEq.html)

[^94]: [https://doc.rust-lang.org/std/cmp/trait.PartialOrd.html](https://doc.rust-lang.org/std/cmp/trait.PartialOrd.html)

[^95]: [https://doc.rust-lang.org/std/hash/trait.Hash.html](https://doc.rust-lang.org/std/hash/trait.Hash.html)

[^96]: The so-called Universal Function Call Syntax.

[^97]: [https://doc.rust-lang.org/std/ops/index.html](https://doc.rust-lang.org/std/ops/index.html)

[^98]: Associated types and constants will also disqualify a trait.

[^99]: The trait `Sized` is implemented by all types with a compile-time known size.
In the language of generic bounds, trait object methods cannot rely on the fact that `Self: Sized`.

[^100]: This is sometimes called being "thread compatible".

[^101]: [https://doc.rust-lang.org/std/marker/index.html](https://doc.rust-lang.org/std/marker/index.html)

[^102]: I.e., write once, use for many types.

[^103]: When mixing lifetime and type parameters, lifetimes go first: `<'a, T>`.

[^104]: This syntax is necessary to disambiguate a generic call from the `<` operator, while keeping the grammar simple.
It is also required when naming generic types in expression position, like `Option::<u32>::Some(42)`.

[^105]: The `::<>` syntax is not used in type position, because it is not necessary for disambiguation.

[^106]: The symbol `MyWrapper`, without angle brackets, is sometimes called a _type constructor_.
Empty angle brackets are also allowed to follow non-generic symbols, mostly for syntactic completeness.
`i32<>` is equivalent to `i32`.

[^107]: Contrast this to C++: C++ template metaprogramming is similar to Rust generics, but significantly harder to use, because callsites can trigger compiler errors in the definition.
Rust side-steps this issue completely.

[^108]: A note on generic parameters vs associated types.
These are similar, but distinct ways of attaching type information to a trait.
While it is completely possible for a single type `T` to implement `Add<U1>` and `Add<U2>`, it is not possible to implement `Add<U1, Output=u32>` and `Add<U1, Output=u64>` at the same time.

[^109]: Note the Universal Function Call Syntax to refer to a particular trait implementation.

[^110]: `where` clauses can also be empty, which looks silly but is useful for macro authors: `fn foo() -> u32 where { /* ... */ }`.

[^111]: While not present in C (except in C11 via the `_Generic` keyword), function overloading is a popular feature in many other languages.

[^112]: [https://doc.rust-lang.org/std/marker/struct.PhantomData.html](https://doc.rust-lang.org/std/marker/struct.PhantomData.html)

[^113]: [https://doc.rust-lang.org/nomicon/phantom-data.html](https://doc.rust-lang.org/nomicon/phantom-data.html)

[^114]: C++ also has "smart pointers", though it is not as strict about what that means as Rust (none of the smart pointers used in embedded programming in Rust allocate, for example).

[^115]: [https://doc.rust-lang.org/stable/std/ops/trait.Deref.html](https://doc.rust-lang.org/stable/std/ops/trait.Deref.html)

[^116]: Even though raw pointers can be dereferenced with `*ptr`, they do _not_ implement `Deref`.
Similarly, although references implement `Deref`, they are not typically called smart pointers.

[^117]: These traits actually have an inheritance relation: calling by `&self` means you can obviously call by `&mut self`, by reborrowing the unique reference as a shared reference; similarly, if you can call by `&mut self`, you can call by `self`, by taking a unique reference to `self`.
In practice, the compiler is pretty good at inlining away the extra calls and references.

[^118]: Functions defined like `fn foo()` each have a unique, closure-like type that coerces to a function pointer when necessary.

[^119]: This is currently magic, but is likely to become less magic in future versions.

[^120]: See [https://doc.rust-lang.org/std/option/index.html#options-and-pointers-nullable-pointers](https://doc.rust-lang.org/std/option/index.html#options-and-pointers-nullable-pointers)

[^121]:  [https://doc.rust-lang.org/std/num/struct.NonZeroI32.html](https://doc.rust-lang.org/std/num/struct.NonZeroI32.html)

[^122]: While it seems we could write `Result<T, !>`, this can't be done on stable.
Uses of `!`, except as the return value of a function, require a nightly compiler.

[^123]: Note that Rust supports error conversion: if the return type error implements `From<E>`, where E is the error type in the `?` expression, it will use that to perform an automatic conversion.

[^124]: As in an electrical fuse: eventually, the fuse goes off and stops working.

[^125]: These being Rust source-code symbols, _not_ linker symbols.

[^126]: [https://doc.rust-lang.org/std/cell/struct.UnsafeCell.html](https://doc.rust-lang.org/std/cell/struct.UnsafeCell.html)

[^127]: `UnsafeCell` (or, the effect it has on data, at any rate) is well-known to the optimizer and the code generator.
As we'll see below, the presence of `UnsafeCell` can radically change how a value is laid out in memory, even though it logically only contains a `T`.

[^128]: [https://doc.rust-lang.org/std/cell/struct.Cell.html](https://doc.rust-lang.org/std/cell/struct.Cell.html)

