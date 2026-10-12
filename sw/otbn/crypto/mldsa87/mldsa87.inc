/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Constants and macros common to all ML-DSA-87 routines. */

.ifndef MLDSA87_INC
.set MLDSA87_INC, 1

/*
 * Mode identifiers. The keygen and sign values must match the ones declared in
 * the cryptolib files `sw/device/lib/crypto/include/mldsa.h` and
 * `sw/device/lib/crypto/impl/mldsa/mldsa.c`.
 */
.equ MLDSA87_MODE_KEYGEN_RND, 0x5514edb7
.equ MLDSA87_MODE_KEYGEN_DET, 0xfaacd725
.equ MLDSA87_MODE_SIGN_ABRIDGED, 0x29d8e5c9
.equ MLDSA87_MODE_SIGN_RND, 0x7138777c
.equ MLDSA87_MODE_SIGN_DET, 0x8accea7f
.equ MLDSA87_MODE_VERIFY, 0x1f9b0e52

/*
 * ML-DSA-87 parameters (FIPS-204, Table 1).
 */
.equ MLDSA87_Q, 8380417      /* Modulus, 2^23 - 2^13 + 1. */
.equ MLDSA87_D, 13           /* Dropped bits from t. */
.equ MLDSA87_TAU, 60         /* Number of +/-1's in the challenge polynomial. */
.equ MLDSA87_GAMMA1, 524288  /* Coefficient range of y, 2^19. */
.equ MLDSA87_GAMMA2, 261888  /* Low-order rounding range, (q - 1) / 32. */
.equ MLDSA87_K, 8            /* Rows of A. */
.equ MLDSA87_L, 7            /* Columns of A. */
.equ MLDSA87_BETA, 120       /* tau * eta. */
.equ MLDSA87_OMEGA, 75       /* Max number of 1's in the hint h. */

/**
 * Wrap a `jal` instruction and perform an instruction count check on the called
 * routine. If the check fails, the program will be trapped.
 *
 * This macro executes 7 instructions if `num_insn` < 2047 and 8 instructions
 * otherwise.
 *
 * @param func The symbol name of the wrapped routine.
 * @param num_insn The expected number of instructions executed by `func`.
 */
.macro jal_fi, func, num_insn
  /* Push the current instruction count onto the call stack. */
  csrrs x1, INSN_CNT, x0
  /* Call the routine and read the new instruction count into x20. */
  jal x1, \func
  csrrs x20, INSN_CNT, x0
  /* Load the expected number of instructions into x21 and add 2 because macro
     has executed 2 instructions since pushing the first instruction count onto
     the stack. */
  li x21, \num_insn
  addi x21, x21, 2
  /* Re-compute the number of instructions before the `jal`. */
  sub x20, x20, x21
  /* Check that the value in x20 matches the one on the call stack. In the
     positive case, perform an explicit long branch since a simple `beq` might
     expand to a different number of instructions depending on the relative
     address of `fatal_error`. Reading from x1 will pop the count from the call
     stack. */
  beq x1, x20, 1f
  jal x0, fatal_error
1:
.endm

/**
 * Push general-purpose registers onto the stack.
 *
 * This macro executes 2 instructions per register.
 *
 * @param regs The registers to push.
 */
.macro push, regs:vararg
  .irp reg, \regs
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr
.endm

/**
 * Pop general-purpose registers from the stack.
 *
 * The registers must be given in the reverse order of the matching `push`.
 *
 * This macro executes 2 instructions per register.
 *
 * @param regs The registers to pop.
 */
.macro pop, regs:vararg
  .irp reg, \regs
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr
.endm

.endif /* MLDSA87_INC */
