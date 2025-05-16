# OTBN Assembly Style Guide

Where possible, OTBN assembly should follow the same principles as the [RISC-V assembly style guide](./asm_coding_style.md).
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

### Handling secret shares

The following guidelines were determined with the [help of the COCO-Alma tool](https://github.com/lowRISC/opentitan/tree/master/hw/ip/otbn/pre_sca/alma) and help protect against SCA attacks.

**1. Do not overwrite a share with its counterpart share.**

A register or memory location which contains one share must not be overwritten with its counterpart. The following lines would each violate this rule and cause transient leakage:
```armasm
/* Leakage (if w0, w1 contain two shares of a secret) */
bn.and  w1, w0, w0
bn.addi w1, w0, 0x0
bn.mov  w1, w0
bn.sel  w1, w0, w0, FG0.C
```

**2. Do not use multiple shares in a single instruction without masking.**

Shares may interact with each other in the ALU and cause stable leakage at a gate or a register.
The following lines would each violate this rule and cause stable leakage:
```armasm
/* Leakage (if w0, w1 contain two shares of a secret) */
bn.add w4, w1, w0
bn.xor w4, w1, w0
```

**3. Do not access shares within successive instructions.**

By violating this rule, one can cause a transient leakage.
Try to reorder the program or interleave the instructions.
If this is not possible, use a dummy instruction.
See following example as a dummy instruction usage.
```armasm
/* Leakage (if w0, w1 contain two shares of a secret) */
bn.xor w4, w0, w0
bn.xor w5, w1, w1

/* No leakage */
bn.xor w4, w0, w0
bn.xor w9, w9, w9 /* dummy instruction */
bn.xor w5, w1, w1
```

**4. Do not have shares even in different bits of a register.**

Even when the shares are in different indexes, this may still cause a stable leakage due to the ECC bit computation.
The following lines are an example of a leakage:

```armasm
/* Leakage (if the LSBs of w0, w1 contain two shares of a secret) */
bn.xor  w9, w9, w9 /* set w9 to zero */
bn.rshi w1, w1, w9 >> 254
bn.xor  w4, w1, w0
```

**5. Be careful with addition and subtraction instructions.**

The following code will mask the share in `w0` with a random value at first and then add the mask to itself.
Since the addition and subtraction operation in the LSB bit is simply an xor operation the mask would be removed for the LSB bit and the last instruction will cause a leakage.
```armasm
/* No leakage */
bn.wsrr  w2, URND   /* mask */
bn.xor   w0, w2, w0
bn.xor   w9, w9, w9 /* dummy instruction */
bn.xor   w4, w1, w0

/* Leakage (if w0, w1 contain two shares of a secret) */
bn.wsrr  w2, URND
bn.xor   w0, w2, w0
bn.add   w0, w2, w0
bn.xor   w9, w9, w9 /* dummy instruction */
bn.xor   w4, w1, w0
```

**6. Do not use a source as the destination of the `bn.sel` instruction if the selection flag is secret.**

The following code will cause a power leakage if `FG0.C` is secret because the Hamming Distance between `w5` to `w5` is zero.
```armasm
/* Leakage (if FG0.C is secret) */
bn.sel w5, w5, w4, FG0.C

/* No leakage */
bn.wsrr w6, URND /* mask */
bn.sel  w6, w5, w4, FG0.C
bn.wsrr w5, URND /* overwrite w5 with a random value */
bn.mov  w5, w6
```

**7. Do not use two shares of the same secret as the sources of the `bn.sel` instruction.**

Due to [blanking limitations](https://github.com/lowRISC/opentitan/blob/ef42c7498534583141e16a6cd5c8df9e4c041bb2/hw/ip/otbn/rtl/otbn_controller.sv#L1018-L1030) of the bn.sel instruction, do not use shares of the same secret as the sources of `bn.sel`.
This would cause a transient leakage.
```
bn.sel w4, w1, w0, FG0.C
```

**8. Clear `ACC` and flags between `bn.mulqacc` instructions which use shares of the same secret.**

It is also necessary to use a dummy instruction to eliminate the transient leakage.
Be aware there are some [flag blanking limitations](https://github.com/lowRISC/opentitan/blob/82bcfcae473e779a77fdabd789476b479cca0077/hw/ip/otbn/rtl/otbn_alu_bignum.sv#L257-L266) on `bn.mulqacc` instructions.
Note that only the writeback versions of `bn.mulqacc` (`bn.mulqacc.wo` and `bn.mulqacc.so`) affect flags.
```armasm
/* Leakage (if w0, w1 contain two shares of a secret) */
bn.mulqacc.wo w6, w4.0, w0.0, 0, FG0
bn.mulqacc.wo w7, w5.0, w1.0, 0, FG0

/* No leakage; clear ACC and flags before using the same flagset */
bn.xor        w9, w9, w9             /* create a zero register */
bn.mulqacc.wo w6, w4.0, w0.0, 0, FG0
bn.wsrw       ACC, w9                /* clear ACC */
bn.mulqacc.wo w9, w9.0, w9.0, 0, FG0 /* clear flags, dummy instruction */
bn.mulqacc.wo w7, w5.0, w1.0, 0, FG0

/* No leakage; clear ACC before using a different flagset */
bn.xor        w9, w9, w9             /* create a zero register */
bn.mulqacc.wo w6, w4.0, w0.0, 0, FG0
bn.wsrw       ACC, w9                /* clear ACC */
bn.wsrw       ACC, w9                /* dummy instruction */
bn.mulqacc.wo w7, w5.0, w1.0, 0, FG1
```

**9. Clear flags after using instructions which set some flags depending on the secret values.**

It is good practice to use the same instruction with non-secret inputs to clear the flags which may include secret shares.
Since not all of the flags are updated by every instruction type, use the same type of instruction as a dummy instruction to clear flags.
```armasm
bn.mulqacc.wo w6, w4.0, w0.0, 0, FG0
bn.mulqacc.wo w9, w9.0, w9.0, 0, FG0 /* clear flags */

bn.sub w4, w4, w0
bn.sub w9, w9, w9 /* clear flags */
```

**10. Apply fresh masking for specific scenarios when needed.**

This is a specific scenario that we have come across when analysing the ECC keygen algorithm with the formal masking verification tool.
Here you can find a simplified code snippet.
In summary, there may be some glitches on the bignum flag computation datapath.
Because of this, masked secret values in different indices come together, mask values may cancel each other out and the separation between the shares may not be preserved.
To fix that, fresh masking can be applied as you can see in the code snippet below.
```armasm
/**
 * Let's assume that after running a program we have following shares in the LSB two bits:
 * w4 = {mask, s0[0]}
 * w5 = {s1[1], s1[0] ^ mask}
 * If we run the following instruction, there will be a transient leakage
 * because w4[1] ^ w4[0] ^ w5[0] == s0[0] ^ s1[0].
 */
bn.xor   w7, w5, w4

/* To fix that, fresh masking can be applied. */
bn.wsrr  w8, URND /* fresh mask */
bn.xor   w8, w31, w3
/* w5 = w5 ^ fresh_mask = {s1[1] ^ f_m[1], s1[0] ^ mask ^ f_m[0]} */
bn.xor   w5, w5, w8
bn.xor   w31, w31, w31 /* dummy instruction */
/* w7 = w4 ^ w5 = {mask ^ s1[1] ^ f_m[1], s0[0] ^ s1[0] ^ mask ^ f_m[0]} */
bn.xor   w7, w5, w4
bn.xor   w31, w31, w31
/* w7 = w7 ^ fresh_mask = {mask ^ s1[1], s0[0] ^ s1[0] ^ mask} */
bn.xor   w7, w7, w8
```

### Copying register values

Prefer `bn.mov <wrd>, <wrs>` to `bn.addi <wrd>, <wrs>, 0` when copying data between registers.
Because `bn.addi` passes data through the ALU, it will strip off integrity protection, while `bn.mov` will copy the integrity protection bits.

### Constant time code

***In cryptographic code, subroutines should always document whether they run in constant or variable time.***

In situations where constant- and variable- time code is mixed, it is recommended to name variable-time subroutines something that makes it clear they are variable-time, such as a name that ends in `_var`.
If a piece of code is constant-time with respect to some inputs but not others (e.g. with respect to the `MOD` register but not to the operands), this should be documented.

Example:
```armasm
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
