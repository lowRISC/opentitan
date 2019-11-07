---
title: "RISC-V Assembly Style Guide"
---

## Basics

### Summary

OpenTitan needs to implement substantial functionality directly in RISC-V assembly.
This document describes best practices for both assembly `.S` files and inline assembly statements in C and C++.
It also codifies otherwise unwritten style guidelines in one central location.

This document is not an introduction to RISC-V assembly; for that purpose, see the [RISC-V Assembly Programmer's Manual](https://github.com/riscv/riscv-asm-manual/blob/master/riscv-asm.md).

Assembly is typically very specialized; the following rules do not presume to describe every use-case, so use your best judgement.

This style guide is specialized for R32IMC, the ISA implemented by Ibex. 
As such, no advice is provided for other RISC-V extensions, though this style guide is written such that advice for other extensions could be added without conflicts.

## General Advice

### Register Names

***When referring to a RISC-V register, they must be referred to by their ABI names.***

See the [psABI Reference](https://github.com/riscv/riscv-elf-psabi-doc/blob/master/riscv-elf.md#register-convention) for a reference to these names.

Example:
```S
  // Correct:
  li a0, 42
  // Wrong:
  li x10, 42
```

This rule can be ignored when the ABI meaning of a register is unimportant, e.g., such as when clobbering all 31 general-purpose registers.

### Pseudoinstrucions

***When performing an operation for which a pseudoinstruction exists, that pseudoinstruction must be used.***

Pseudoinstructions make RISC-V's otherwise verbose RISC style more readable; for consistency, these must be used where possible.

Example:
```S
  // Correct:
  sw t0, _my_global, t1
  // Wrong:
  la t1, _my_global
  sw t0, 0(t1)

  // Correct:
  ret
  // Wrong:
  jr ra
```

### Operation-with-immediate mnemonics

***Do not use aliases for opertaion-with-immediate instructions, like `add rd, rs, imm`.***

Assemblers usually recognize instructions like `add t0, t1, 5` as an alias for `addi`. These should be avoided, since they are confusing and a potential source of errors.

Example:
```S
  // Correct:
  addi t0, t1, 0xf
  ori  a0, a0, 0x4
  // Wrong:
  add  t0, t1, 0xf
  or   a0, a0, 0x4
```

### Loading Addresses

***Always use `la` to load the address of a symbol; always use `li` to load an address stored in a `#define`.***

Some assemblers allow `la` with an immediate expression instead of a symbol, allowing a form of symbol+offset.
However, support for this behavior is patchy, and the semantics of PIC `la` with immediate are unclear (in PIC mode, `la` should perform a GOT lookup, not a `pc`-relative load).

### Jumping into C

***Jumping into a C function must be done either with a `call` instruction, or, if that function is marked `noreturn`, a `tail` instruction.***

The RISC-V jump instructions take a "link register", which holds the return address (this should always be `zero` or `ra`), and a small `pc`-relative immediate.
For jumping to a symbol, there are two user-controlled settings: "near" or "far", and "returnable" (i.e., a link register of `zero` or `ra`).
The mnemonics for these are:
- `j sym`, for a near non-returnable jump.
- `jal sym`, for a near returnable jump.
- `tail sym`, for a far non-returnable jump (i.e., a non-unwinding tail-call).
- `call sym`, for a far returnable jump (i.e., function calls).

Far jumps are implemented in the assembler by emiting `auipc` instructions as necessary (since the jump-and-link instruction takes only a small immediate).
Jumps into C should always be treated as far jumps, and as such use the `call` instruction, unless the C function is marked `noreturn`, in which case `tail` can be used.

Example:
```S
  call _syscall_start

  tail _crt0
```

### Control and Status Register (CSR) Names

***CSRs defined in the RISC-V spec must be refered to by those names (like `mstatus`), while custom non-standard ones must be encapsulated in a `#define`.***

Naturally, if a pseudoinstruction exists to read that CSR (like `rdtime`) that one should be used, instead.

`#define`s for CSRs should be prefixed with `CSR_<design>_`, where `<design>` is the name of the design the CSR corresponds to.

Recognized CSR prefixes:
- `CSR_IBEX_` - A CSR specific to the Ibex core.
- `CSR_OT_` - A CSR specific to the OpenTitan chip, beyond the Ibex core.

Example:
```S
  csrr t0, mstatus

  #define CSR_OT_HMAC_ENABLED ...
  csrw CSR_OT_HMAC_ENABLED, 0x1
```

### Load and Store From Pointer in Register

***When loading and storing from a pointer in a register, prefer to use `n(reg)` shorthand.***

In the case that a pointer is being read without an offset, prefer `0(reg)` over `(reg)`.

```S
  // Correct:
  lw t3, 8(sp)
  sb t3, 0(a0)
  // Wrong:
  lw t3, sp, 8
  sb t3, a0
```

### Compressed Instruction Mnemonics

***Do not use compressed instruction mnemonics.***

While Ibex implements the RISC-V C extension, it is expected that the toolchain will automatically compress instructions where possible.

Of course, this advice should be ignored when it is necessary to prove that a certain block of instructions does not exceed a particular width.

### "Current Point" Label

***Do not use the current point (`.`) label.***

The current point label does not look like a label, and can be easilly missed during review.

## `.S` Files

This advice applies specifically to `.S` files, as well as globally-scoped assembly in `.c` and `.cc` files.

While this is is already implicit, we only use the `.S` extension for assembly files; not `.s` or `.asm`.

### Indentation

Assembly files must be formatted with all directives indented two spaces, except for labels.
Comments should be indented as usual.

There is no mandated requirement on aligning instruction operands.

Example:
```S
_trap_start:
  .globl _trap_start
  csrr a0, mcause
  sw x1, 0(sp)
  sw x2, 4(sp)
  // ...
```

### Comments

***Comments must use either the `//` or `/* */` syntaxes.***

Every function-like label which is meant to be called like a function (*especially* `.globl`s) should be given a Doxygen-style comment.
While Doxygen is not suited for assembly, that style should be used for consistency.
See the [C/C++ style guide]({{< relref "c_cpp_coding_style" >}}) for more information.

All other advice for writing comments, as in the C/C++ style guide, also applies.

### Register useage

***Register usage in a "function" that diverges from the RISC-V function call ABI must be documented.***

This includes non-standard calling conventions, non-standard clobbers, and other behavior not expected of a well-behaved RISC-V function.
Non-standard input and output registers should use Doxygemn's `param[in] reg` and
`param[out] reg` annotations, respectively.

Within a function, whether or not it conforms to RISC-V's calling convention, comments should be present to describe the asassignment of logical values to registers.

Example:
```S
/**
 * Compute some stuff, outputing a 96-bit integer.
 *
 * @param[out] a0 bits [31:0] of the result.
 * @param[out] a1 bits [63:32] of the result.
 * @param[out] a2 bits [95:64] of the result.
 */
compute_stuff:
  .globl compute_stuff
  // a0 is to be used as an accumulator, which will be returned as-is.
  li a0, 0xdeadbeef
  // t0 is a loop variable.
  li t0, 0x0
1:
  // ...
  bnez t0, 1b

  li   a1, 0xbeefcafe
  li   a2, 0xcafedead
  ret
```

### Ending an Instruction Sequence

***Every code path within an assembly file must end in a non-linking jump.***

Assembly should be written such that the program counter can't wander off past the written instructions.
As such, all assembly should be ended with `ret` (or any of the protection ring returns like `mret`), an infinite `wfi` loop, or an instruction that is guaranteed to trap and not return, like an `exit`-like syscall or `unimp`.

Example:
```S
loop_forever:
  wfi
  j loop_forever
```

### Alignment Directives

***Do not use `.align`; use `.p2align` and `.balign` as the situation requires.***

The exact meaning of `.align` depends on architecture; rather than asking readers to second-guess themselves, use alignment directives with strongly-typed arguments.

Example:
```S
  // Correct:
  .balign 8 // 8-byte aligned.
  tail _magic_symbol

  // Wrong:
  .align 8 // Is this 8-byte aligned, or 256-byte aligned?
  tail _magic_symbol
```

### Inline Binary Directives

***Always use `.byte`/`.2byte`/`.4byte`/`.8byte` for inline binary data.***

`.word`, `.long`, and friends are confusing, for the same reason `.align` is.

## Inline Assembly

This advice applies to function-scope inline assembly in `.c` and `.cc` files.
For an introduction on this syntax, check out [GCC's documentation](https://gcc.gnu.org/onlinedocs/gcc/Extended-Asm.html).

### When to Use

***Avoid inline assembly as much as possible, as long as correctness and readability are not impacted.***

Inline assembly is best reserved for when a high-level language cannot express what we need to do, such as expressing complex control flow or talking to the hardware.
If a compiler intrinsic can achieve the same effect, such as `__builtin_clz()`, then that should be used instead.

> The compiler is *always* smarter than you; only in the rare case where it is not, assembly should be used instead.

### Formatting

Inline assembly statements must conform to the following formatting requirements, which are chosen to closely resemble how Google's clang-format rules format function calls.
- Neither the `asm` or `__asm__` keyword is specified in C; the former must be used, and should be `#define`d into existence if not supported by the compiler.
  C++ specifies `asm` to be part of the grammar, and should be used exclusively.
- There should not be a space after the `asm` qualfiers and the opening parentheses:
  ```c
  asm(...);
  asm volatile(...);
  ```
- Single-instruction `asm` statements should be written on one line, if possible:
  ```c
  asm volatile("wfi");
  ```
- Multiple-instruction `asm` statements should be written with one instruction per line, formatted as follows:
  ```c
  asm volatile(
    "my_label:"
    "  la   sp, _stack_start;"
    "  tail _crt0;"
    ::: "memory");
  ```
- The colons separating register constraints should be surrounded with spaces, unless there are no constraints between them, in which case they should be adjacent.
  ```c
  asm("..." : "=a0"(foo) :: "memory");
  ```

### Non-returning `asm`

***Functions with non-returning `asm` must be marked as `noreturn`.***

C and C++ compilers are, in general, not supposed to introspect `asm` blocks, and as such cannot determine that they never return.
Functions marked as never returning should end in `__builtin_unreachable()`, which the compiler will usually turn into an `unimp`.

