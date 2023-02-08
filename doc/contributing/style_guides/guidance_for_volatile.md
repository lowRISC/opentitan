---
title: "Guidance for `volatile` in OpenTitan Silicon Creator Code"
---

## TL;DR

Do not use `volatile` in production, i.e. non-test, silicon creator code unless you are implementing a library explicitly for this purpose like `sec_mmio`, `abs_mmio`, or `hardened`.
Specifically, do not use `volatile` for

*   Accessing memory-mapped registers,
    *   _Instead, use `sec_mmio` or `abs_mmio`_.
*   Hardening purposes.
    *   _Instead, use the primitives in `hardened.h`._
*   Variables initialized outside the lifetime of the program, e.g. a pointer to some data in flash or retention SRAM, or
    *   _Instead, declare as non-`const `and non-`volatile`. Use a getter to enforce `const`-ness if needed._
*   Pointers created out of thin air.
    *   _Compiler cannot optimize the first access (assuming that the pointer doesn't point to something already known by the compiler)._

Do use `volatile` if a variable is shared between an interrupt/exception handler and the rest of the on-target test program to ensure correctness.
*   _Since silicon creator code does not use handlers in the conventional sense, this essentially limits `volatile` usage to on-target tests._

When in doubt, please do not hesitate to reach out by creating a GitHub issue (preferably with the "Type:Question" label).

## Introduction

The goal of this document is to provide guidance for using `volatile` in OpenTitan Silicon Creator code, i.e. `rom`, `rom_ext`, related tests, and examples.
There are several reasons for this guidance:

*   `volatile` is contagious and, similar to `const`-correctness, `volatile`-correctness can be hard to achieve and maintain. Once a variable is declared as `volatile`, the `volatile` keyword must appear throughout the call stack in all other variables that will reference the same object.
*   `volatile` pointers cannot be passed as arguments to standard functions such as `memcpy`, `memset`, etc. Casting `volatile`-ness away in such cases results in undefined behavior. This is an easy-to-make but hard-to-catch mistake.
*   Semantic meaning of `volatile` is not very clear and it can have significant effects on the size and efficiency of the generated code. Often what we want is `volatile` access or forced loads/stores as opposed to the type of the variable being `volatile`. `abs_mmio` and `sec_mmio` libraries, for example, implement `volatile` access for memory mapped registers.

Review the links provided in the References section for more information and some criticism on `volatile`.

## An Intuitive Definition of `volatile`

Consider the following toy example:
```
static bool my_var = false;

void my_function(void) {
    my_var = true;
    // Code that doesn't touch `my_var`
    ...
    if (my_var) {  // <- `my_var` must be `true`.
        ...
    } else {
        ...
    }
}
```
Since the value of `my_var` is guaranteed to be `true`, an optimizing compiler can optimize away the comparison and the `else` branch.
Now, assume we add an ISR that resets `my_var`:
```
static bool my_var = false;

// `my_isr` can modify `my_var` at any time but the compiler doesn't know that.
void my_isr(void) {
    my_var = false;
}

void my_function(void) {
    my_var = true;
    // Code that doesn't touch `my_var` and doesn't call `my_isr()`.
    ...
    if (my_var) {  // <- The compiler would think that `my_var` must be `true`.
        ...
    } else {
        ...
    }
}
```
Using the same kind of analysis, an optimizing compiler would reach the same conclusion as in the previous example, i.e. optimize away the comparison along the else branch, and break our program.
This is where `volatile` comes into play:
```
// `volatile`: `my_var` may be modified in ways unknown to the implementation.
static volatile bool my_var = false;

// Indeed, `my_isr` can modify `my_var` at any time.
void my_isr(void) {
    my_var = false;
}

void my_function(void) {
    my_var = true;
    // Code that doesn't touch `my_var` and doesn't call `my_isr()`.
    ...
    if (my_var) {  // <- Cannot remove this check since `my_var` may be modified
        ...        //    in ways unknown to the implementation.
    } else {
        ...
    }
}
```
In this case, an optimizing compiler cannot optimize away the comparison since the value of `my_var` may have changed since it has been set to `true`.

## Rule 1: No `volatile` in Production Silicon Creator C Code[^1]

Cases like the example above, however, do not typically appear in _production, i.e. non-test,_ silicon creator C code since we don't enable interrupts and our handlers shut down the chip instead of returning.
Thus, `volatile` should not be used in _production_ silicon creator C code.
The following subsections cover the four most relevant cases where `volatile` might be considered and the rationale behind this guidance.

### Memory-Mapped Registers

`abs_mmio` and `sec_mmio` libraries already encapsulate `volatile` access semantics.
When accessing memory mapped registers, any new code must use `abs_mmio` or `sec_mmio` libraries instead of declaring `volatile` pointers or performing `volatile` accesses by casting at the point of dereferencing.

### Hardening

Do not use `volatile` for hardening purposes.
OpenTitan has invested considerably to define simple and predictable building blocks and to leverage them to harden various patterns in `rom` and `rom_ext`.
See `hardened.h` for the hardening primitives we have.

### `const` and Non-`const` Variables Initialized Outside the Lifetime of a Program

There are several cases in OpenTitan silicon creator code where a variable with static storage duration is initialized either partially or completely in a way that isn’t visible to the C source code overriding the static initializer of the C object.
A `const` example to this case is the definition of `kManifest` in `sw/device/silicon_creator/lib/manifest_def.c`.
`kManifest` is an aggregate object of type `manifest_t` that resides in flash memory whose actual value at runtime is different from the initializer in source code because the binary is modified by the build system before it is loaded into flash memory.
Non-`const` examples include the `struct`s in the `static_critical` section of the main SRAM.

Such variables must be declared as
*   non-`const`, and
    *   _Rationale: Even if the object resides in read-only memory, it must not be declared as a `const`-qualified type. If `const` is used, the compiler is not required to allocate space for the object and may replace reads with the value specified in the initializer. If needed, `const` related compiler diagnostics must be enabled by providing a getter that returns a `const` pointer to the actual object instead of exposing the non-`const` declaration._
*   non-`volatile`.
    *   _Rationale: The `volatile` qualifier prevents various optimizations and the use of `memcpy`, `memset`, and many other standard functions. The specification states that "All objects with static storage duration shall be initialized (set to their initial values) before program startup. The manner and timing of such initialization are otherwise unspecified." (C11, section 5.1.2, paragraph 1). By not using `volatile` we’re no longer informing the compiler that the value of the object "may be modified in ways unknown to the implementation" (C11, section 6.7.3, paragraph 7). In principle, this could be problematic in situations where the implementation is allowed to assume that the object contains its initial value, e.g. when the object is `const` or when performing LTO and the compiler assumes that it has visibility into the whole program (using the `-fwhole-program` flag in gcc)_[^2]_. Since neither of these are true in this case, it seems safe to conclude that the compiler has to be conservative and cannot assume that the object has not been modified since the program startup._

### Pointers Created Out of Thin Air

OpenTitan secure boot consists of at least three stages: `rom`, `rom_ext`, and the first owner boot stage.
All boot stages except `rom` are stored in flash and all in-flash boot stages are required to start with a "manifest" so that their integrity and authenticity can be verified.
Since OpenTitan uses a fixed flash layout, `rom` and `rom_ext` exactly know the next stage's manifest's location in flash.
Since this address is not part of their images, `rom` and `rom_ext` create pointers essentially out of thin air using functions like `_const manifest_t *boot_policy_manifest_a_get(void)_`.
If the pointers in question do not point to something already known by the compiler, an optimizing compiler cannot optimize away the first access.
Thus, there is no need to declare such pointers as `volatile`.

## Rule 2: Use `volatile` in Tests For Correctness

`rom` and `rom_ext` do not enable interrupts and their handlers shut down the chip instead of returning.
Tests, however, can define their custom interrupt/exception handlers for their own purposes.
In cases where a variable is shared between a handler and the rest of the program, it must be declared as `volatile` to ensure correctness.

## References

*   [Final draft of C11](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf)
*   [Deprecating volatile - JF Bastien - CppCon 2019](https://www.youtube.com/watch?v=KJW_DLaVXIY): A longer discussion on `volatile` and c++ with a good set of demotivating examples in the first 20+ minutes
*   [LLVM Language Reference Manual — LLVM 16.0.0git documentation](https://llvm.org/docs/LangRef.html#volatile-memory-accesses)
*   PRs that implement the guidance in this doc: [#15253](https://github.com/lowRISC/opentitan/pull/15253), [#15286](https://github.com/lowRISC/opentitan/pull/15286), [#15287](https://github.com/lowRISC/opentitan/pull/15287), [#15302](https://github.com/lowRISC/opentitan/pull/15302), [#15303](https://github.com/lowRISC/opentitan/pull/15303).

## Notes

[^1]: This rule does not apply to libraries written specifically to leverage or encapsulate `volatile` semantics such as `abs_mmio`, `sec_mmio`, or `hardened`.

[^2]: We can prevent such optimizations by adding `asm volatile("" : : : "memory")` at the entry point when using LTO but that seems unnecessary in practice. `-fwhole-program` is not supported by Clang and the more fine-grained flags that Clang has for similar purposes don't seem to interact with this issue.
