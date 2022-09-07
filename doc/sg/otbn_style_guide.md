---
title: "OTBN Assembly Style Guide"
---

Where possible, OTBN assembly should follow the same principles as the [RISC-V assembly style guide]({{< relref "asm_coding_style" >}}).
This guide describes additional OTBN-specific guidelines, and places where OTBN assembly can or should diverge from the RISC-V style guidelines.

## General Advice

### Register Names

There's no ABI, so OTBN registers cannot be referred to by ABI names.

### Capitalization

Lower case for mnemonics and registers.

Example:
```S
  /* Correct */
  bn.addi   w3, w3, 2

  /* Wrong */
  BN.ADDI   W3, W3, 2
```

Upper case for flags, flag groups, and half word identifiers in multiplication instructions.
Example:
```S
  /* Correct */
  bn.mulqacc.so  w27.L, w30.0, w25.1, 64
  bn.sel         w3, w4, w2, FG1.C

  /* Wrong */
  bn.mulqacc.so  w27.l, w30.0, w25.1, 64
  bn.sel         w3, w4, w2, fg1.c
```

### Pseudoinstructions

As in RISC-V, prefer pseudoinstructions (e.g. `ret`, `li`) in OTBN code where they exist.
However, `loop` and `loopi` instructions require counting the number of instructions in the loop body, which can be tricky for pseudoinstructions that can expand to multiple instructions.
(For example, `li` can expand to either 1 or 2 instructions depending on the immediate value.)
Therefore, it is permitted to avoid pseudoinstructions that can expand to multiple instructions within loop bodies.

### Wrappers and ecall

Generally, OTBN routines should be written so that they finish in `ret`.
Use of `ecall` should be restricted to thin wrapper files which serve as an interface for the more substantial assembly files, usually just reading one or two arguments and then calling subroutines from the other files.

### Comments

The `//` syntax is not currently available for OTBN because it is not supported by `riscv32-unknown-as`.
Use the `/* */` syntax instead.

### Labels

It is not required to use an `L_` prefix for internal labels.
Labels should not be indented.

### Operand Alignment

***Operands should be aligned within blocks of OTBN code.***

The exact spacing between mnemonic and operand is not important, as long as it is consistent within the block.

Example:
```S
  /* Correct */
  bn.add  w4, w7, w10
  bn.addc w5, w8, w11
  bn.sel  w2, w2, w3, C

  /* Correct */
  bn.add        w4, w7, w10
  bn.addc       w5, w8, w11
  bn.sel        w2, w2, w3, C

  /* Wrong */
  bn.add w4, w7, w10
  bn.addc w5, w8, w11
  bn.sel w2, w2, w3, C
```

### Register and flag group clobbering

***Always document which registers and flag groups are clobbered by an OTBN "function", and which flags have meaning.***

OTBN subroutines should always document the registers and flag groups whose values they overwrite, including those used for output.
In addition to Doxygen-style `@param[in]` and `@param[out]` notations, OTBN subroutines should also state whether the flags have meaning at the end of the subroutine.
If a subroutine jumps to another subroutine that clobbers additional registers or flag groups, these additional names should be added to the caller's list.

Example:
```S
/**
 * Compute the sum of two 2048-bit numbers.
 *
 *   Returns C = A + B.
 *
 * Flags: When leaving this subroutine, the C flag of FG0 depends on the
 *        addition.
 *
 * @param[in]  [w10:w3]: A, first 2048-bit operand
 * @param[in]  [w18:w11]: B, second 2048-bit operand
 * @param[in]  w31: all-zero
 * @param[out] [w26:w19]: C, result
 *
 * clobbered registers: x9 to x13, w19 to w28
 * clobbered flag groups: FG0
 */
wide_sum:
  /* Prepare temporary registers. */
  li       x9, 3
  li       x10, 11
  li       x11, 19
  li       x12, 27
  li       x13, 28

  /* Clear flags. */
  bn.add   w31, w31, 0

  /* Addition loop. */
  loopi    8, 4
    /* w27 <= A[i] */
    bn.movr  x12, x9++
    /* w28 <= B[i] */
    bn.movr  x13, x10++
    /* w27 <= w27 + w28 */
    bn.addc  w27, w27, w28
    /* C[i] <= w27 */
    bn.movr  x11++, x12

  ret
```

### Alignment Directives

Big-number load/store instructions (`bn.lid`, `bn.sid`) require DMEM addresses
to be 256-bit aligned; use `.balign 32` for any big-number inline binary data
to ensure this. For non-big-number data, `.balign 4` (32-bit alignment) is
recommended.

### Inline Binary Directives

Prefer `.word` over alternatives such as `.quad`.

## Secure Coding for Cryptography

The following guidelines address cryptography-specific concerns for OTBN assembly.

### Copying register values

Prefer `bn.mov <wrd>, <wrs>` to `bn.addi <wrd>, <wrs>, 0` when copying data between registers.
Because `bn.addi` passes data through the ALU, it will strip off integrity protection, while `bn.mov` will copy the integrity protection bits.

### Constant time code

***In cryptographic code, subroutines should always document whether they run in constant or variable time.***

In situations where constant- and variable- time code is mixed, it is recommended to name variable-time subroutines something that makes it clear they are variable-time, such as a name that ends in `_var`.
If a piece of code is constant-time with respect to some inputs but not others (e.g. with respect to the `MOD` register but not to the operands), this should be documented.

Example:
```S
/**
 * Determine if two 2048-bit operands are equal.
 *
 *   Returns 1 if A = B, otherwise 0.
 *
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  [w10:w3]: A, first 2048-bit operand
 * @param[in]  [w18:w11]: B, second 2048-bit operand
 * @param[in]  w31: all-zero
 * @param[out] x3: result, 1 or 0
 *
 * clobbered registers: x2, x3, x6, x9 to x12
 * clobbered flag groups: FG0
 */
eq_2048:

  /* Prepare temporary registers. */
  li       x9, 3
  li       x10, 11
  li       x11, 27
  li       x12, 28

  /* Check if all limbs are equal. */
  li       x3, 1
  loopi    8, 4
    /* w27 <= A[i] */
    bn.movr  x11, x9++
    /* w28 <= B[i] */
    bn.movr  x12, x10++
    /* x2 <= (w27 == w28) */
    jal      x1, eq_256
    /* x3 <= x3 & x2 */
    and      x3, x2, x2

  ret

/**
 * Determine if two 2048-bit operands are equal.
 *
 *   Returns 1 if A = B, otherwise 0.
 *
 * This routine runs in variable time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  [w10:w3]: A, first 2048-bit operand
 * @param[in]  [w18:w11]: B, second 2048-bit operand
 * @param[in]  w31: all-zero
 * @param[out] x2: result, 1 or 0
 *
 * clobbered registers: x2, x6, x9 to x12
 * clobbered flag groups: FG0
 */
eq_2048_var:

  /* Prepare temporary registers. */
  li       x9, 3
  li       x10, 11
  li       x11, 27
  li       x12, 28

  /* Check if all limbs are equal. */
  li       x2, 1
  loopi    8, 5
    /* If x2 is 0, skip to the end of the loop. (It's still necessary to
       complete the same number of loop iterations to avoid polluting the loop
       stack, but we can skip all instructions except the last.) */
    beq      x2, x0, loop_end
    /* w27 <= A[i] */
    bn.movr  x11, x9++
    /* w28 <= B[i] */
    bn.movr  x12, x10++
    /* x2 <= (w27 == w28) */
    jal      x1, eq_256
loop_end:
    nop

  ret
```
