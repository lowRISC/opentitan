/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Various finite-field rounding routines. */

.globl shift_left
.globl decompose

.text

/**
 * Multiply the coefficients of a polynomial by 2^d = 2^13.
 *
 * This routine implements the shift of the t1 vector coefficients as part of
 * the ML-DSA verify function. The coefficients are assumed to be in the
 * interval [0, 2^10 - 1]. d = 13 is common to all ML-DSA variants.
 *
 * @param[in] x2: DMEM address of the polynomial.
 * @param[in[ x3: DMEM address of the shifted output polynomial.
 */
shift_left:
  /* Push clobbered registers onto the stack. */
  .irp reg, x2, x3
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* Each iteration shifts 8 coefficients. */
  loopi 32, 3
    bn.lid x0, 0(x2++)
    bn.shv.8S w0, w0 << 13
    bn.sid x0, 0(x3++)
    /* End of loop */

  /* Restore clobbered general-purpose registers. */
  .irp reg, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret

/**
 * Decompose a polynomial W into two polynomials W0 and W1 composed of the
 * lower and higher bits of each coefficient in W respectively.
 *
 * More formally, given a coefficient w of W, this routine computes w0 and w1
 * such that w = w1 * 2*GAMMA2 + w0 mod Q, for w0 in [-(Q / 2) - 1, Q / 2].
 *
 * This is an implementation of the `Decompose` function (Algorithm 36) of
 * FIPS-204.
 *
 * CAUTION: The routine can only be used in ML-DSA-65 and ML-DSA-87 as the
 * different GAMMA2 constant in ML-DSA-44 necessitates a different
 * decomposition algorithm.
 *
 * @param[in] x2: DMEM address of the input polynomial W.
 * @param[in] x3: DMEM address of the output polynomial W0.
 * @param[in] x4: DMEM address of the output polynomial W1.
 */
decompose:
  /* Push clobbered registers onto the stack. */
  .irp reg, x2, x3, x4, x5, x6
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /*
   Proof of correctness:

   ALPHA = (Q - 1) / 16
   ALPHA^-1 = -16 mod Q.

   b = ALPHA^-1 * (w + GAMMA2) - 1 mod Q.
     = ALPHA^-1 * (w + ALPHA / 2) - 1 mod Q
     = ALPHA^-1 * ((w1 * ALPHA + w0) + ALPHA / 2) - 1 mod Q
     = w1 + ALPHA^-1 * (w0 - ALPHA / 2) mod Q
     = w1 + 16 * (ALPHA / 2 - w0).

   Since (ALPHA / 2 - w0) > 0, we have that the four LSBs of b contain w1.
  */

  /* Load the decomposition constants into w3-w8. */
  addi x5, x0, 3
  la x6, _decompose_const_alphas
  bn.lid x5++, 0(x6)    /* w3 = (ALPHA, ALPHA^-1, 0^192) */
  bn.lid x5++, 32(x6)   /* w4 = GAMMA2 */
  bn.lid x5++, 64(x6)   /* w5 = Q */
  bn.shv.8s w6, w5 >> 1 /* w6 = (Q - 1) / 2 */

  bn.not w7, w31
  bn.shv.8s w7, w7 >> 28 /* w7 = (0x0000000f, 0x0000000f, ..., 0x0000000f) */
  bn.shv.8s w8, w7 >> 3  /* w8 = (0x00000001, 0x00000001, ..., 0x00000001) */

  /* WDR pointer to the coefficients of w1. */
  addi x5, x0, 1

  loopi 32, 15
    bn.lid x0, 0(x2++)

    /* b = w + GAMMA2 mod Q. */
    bn.addvm.8s w1, w0, w4

    /* b = ALPHA^-1 * b - 1 mod Q. */
    bn.mulvml.8s w1, w1, w3, 1
    bn.addvm.8s w1, w1, w31 /* cond sub */
    bn.subvm.8s w1, w1, w8

    /* w1 = b & 0xf. */
    bn.and w1, w1, w7

    /* w0 = w - ALPHA * w1. */
    bn.mulvl.8s w2, w1, w3, 0
    bn.subv.8s w0, w0, w2

    /*
     * Reduction step, map w0 into the centered interval [-Q/2-1, Q/2], i.e.,
     * if w0 = w0, if w0 < (Q - 1) / 2, else w0 = w0 - (Q - 1) / 2.
     */

    /* w0 = w0 - (((((Q - 1) / 2) - w0) >> 31) & Q). */
    bn.subv.8s w2, w6, w0
    bn.shv.8s w2, w2 >> 31
    bn.subv.8s w2, w31, w2
    bn.and w2, w2, w5
    bn.subv.8s w0, w0, w2

    bn.sid x0, 0(x3++)
    bn.sid x5, 0(x4++)
    /* End of loop */

  /* Restore clobbered general-purpose registers. */
  .irp reg, x6, x5, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret

.data
.balign 32

/*
 * Decomposition constants.
 *
 * XXX: Potentially move to the *_mem.s files, once the entire application has
 * been assembled as other multiple routines share the same constants.
 */

_decompose_const_alphas:
.word 0x0007fe00 /* ALPHA = 2 * GAMMA1 = (Q - 1) / 16 */
.word 0x007f0009 /* ALPHA^-1 * 2^32 mod Q (Montgomery domain) */
.zero 24 /* Padding */

/* GAMMA2 = (Q - 1) / 32. */
_decompose_const_gamma2:
.word 0x0003ff00
.word 0x0003ff00
.word 0x0003ff00
.word 0x0003ff00
.word 0x0003ff00
.word 0x0003ff00
.word 0x0003ff00
.word 0x0003ff00

/* ML-DSA modulus: Q = 8380417. */
_decompose_const_q:
.word 0x007fe001
.word 0x007fe001
.word 0x007fe001
.word 0x007fe001
.word 0x007fe001
.word 0x007fe001
.word 0x007fe001
.word 0x007fe001
