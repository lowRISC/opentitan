/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Secure masked gadgets. */

.globl sec_bound_check
.globl sec_decompose
.globl sec_mod5_8x32

/**
 * Calculate a secure bound check on the arithmetically shared coefficients of
 * a polynomial.
 *
 * This is a masked variant of the infinity norm check that verifies for a
 * polynomial X that its infinity norm is smaller than a given bound b, i.e.,
 * |X|_inf < b. For a detailed explanation of the inner workings of this
 * algorithm see `mldsa87_verify_norm.s`.
 *
 * This routine implements the `SecBoundCheck` function (Algorithm 5 in [1]).
 *
 * @param[in]  x2: DMEM address of the first arith. share of the polynomial X.
 * @param[in]  x3: DMEM address of the second arith. share of the polynomial X.
 * @param[in]  x4: DMEM address of the vectorized bound b (32 bytes).
 * @param[out] w0: result, 2^32-1 if the |X|_inf < b, else 0.
 */
sec_bound_check:
  /* Push clobbered registers onto the stack. */
  .irp reg, x2, x3, x5, x6
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* Load the bound constant b and subtract 1 from it. */
  bn.lid x0, 0(x4)
  bn.not w1, w31
  bn.shv.8s w1, w1 >> 31
  bn.subv.8s w4, w0, w1

  /* b' = 2 * (b - 1). */
  bn.addv.8S w5, w4, w4

  /* First and second share WDR pointers. */
  addi x5, x0, 0
  addi x6, x0, 1

  bn.not w6, w31 /* flag */

  /* Iterate over the entire polynomial in chunks of 8 coefficients and check
     their infinity norm in parallel. */
  loopi 32, 7
    /* Load the first share x0 and add the bound b, x0 + b mod Q. */
    bn.lid x5, 0(x2++)
    bn.addvm.8S w0, w0, w4

    /* Slot b' into w2 for `seq_leq`. */
    bn.mov w2, w5

    bn.lid x6, 0(x3++)

    /* Convert to Boolean shares and invoke `sec_leq` with b'. */
    jal x1, sec_a2b_8x32
    jal x1, sec_leq_8x32

    bn.and w6, w6, w0
    /* End of loop */

  /* w0 = 2^256 - 1 if |X|_inf < b, else 0. */
  bn.not w0, w31
  bn.cmp w6, w0, FG0
  bn.sel w0, w0, w31, FG0.Z

  /* Restore clobbered general-purpose registers. */
  .irp reg, x6, x5, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret

/**
 * Securely decompose an arithmetically shared polynomial X = X0_A + X1_A into
 * two polynomials W0 = W00_A + W01_A and W1 composed of the lower and higher
 * bits of each coefficient in X respectively. W0 will be arithmetically shared
 * while W1 is unmasked.
 *
 * This routine is a masked variant of the polynomial decomposition. See
 * `mldsa87_verify_rounding.s` for detailed breakdown of the individual
 * computational steps. This is an implementation of the `SecDecompose`
 * function (Algorithm 7 in [1]).
 *
 * Note that this routine will overwrite the inputs X0_A and X1_A with W00_A
 * and W01_A.
 *
 * @param[in] x2: DMEM address of the first input share polynomial X0_A and
 *                the output polynomial W00_A.
 * @param[in] x3: DMEM address of the second input share polynomial X1_A and
 *                the output polynomial W01_A.
 * @param[in] x4: DMEM address of output polynomial W1.
 */
sec_decompose:
  /* Push clobbered registers onto the stack. */
  .irp reg, x2, x3, x4, x5, x6
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* Load decomposition constants into w4-w7. */
  addi x5, x0, 4
  la x6, _sec_decompose_gamma2
  bn.lid x5++, 0(x6)  /* w4 = GAMMA2 */
  bn.lid x5++, 32(x6) /* w5 = (ALPHA, ALPHA^-1) */

  bn.not w6, w31
  bn.shv.8s w6, w6 >> 28 /* w6 = (0x0000000f, 0x0000000f, ..., 0x0000000f) */
  bn.shv.8s w7, w6 >> 3  /* w7 = (0x00000001, 0x00000001, ..., 0x00000001) */

  /* WDR pointers. */
  addi x5, x0, 8  /* x0 */
  addi x6, x0, 9  /* x1 */

  loopi 32, 16
    bn.lid x5, 0(x2)

    /*
     * Part 1: b = ALPHA^-1 * (x0 + GAMMA2) - 1, with b = b0 + b1 mod Q.
     */

    /* b0 = x0 + GAMMA2 mod Q. */
    bn.addvm.8S w0, w8, w4

    /* b0 = ALPHA^-1 * b - 1 mod Q. */
    bn.mulvml.8S w0, w0, w5, 1
    bn.addvm.8S w0, w0, w31 /* cond sub */
    bn.subvm.8S w0, w0, w7

    bn.xor w31, w31, w31 /* dummy */

    /* b1 = ALPHA^-1 * x1 mod Q. */
    bn.lid x6, 0(x3++)
    bn.mulvml.8S w1, w9, w5, 1
    bn.addvm.8S w1, w1, w31 /* cond sub */

    /* Convert (b0, b1) to Boolean shares. */
    jal x1, sec_a2b_8x32
    jal x1, sec_unmask_8x32

    /*
     * Part 2: w1 = (b0 ^ b1) mod 16, w0 = b0 - ALPHA * w1.
     */

    /* w1 = b mod 16. */
    bn.and w0, w0, w6

    /* w0 = b0 - ALPHA * w1. */
    bn.mulvl.8S w1, w0, w5, 0
    bn.subvm.8S w8, w8, w1

    bn.sid x5, 0(x2++)
    bn.sid x0, 0(x4++)
    /* End of loop */

  /* Restore clobbered general-purpose registers. */
  .irp reg, x6, x5, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret


/**
 * Reduce a vector of 8 Boolean-masked coefficients (x0_B, x1_B) in the
 * interval [0, 14] modulo 5.
 *
 * Rationale: A coefficient x in the interval [0, 14] is, with uniform
 * probability, in on of three buckets [0, 4], [5, 9] and [10, 14]:
 *
 *   - [0, 4]: x is already reduced modulo 5 and nothing needs to be done.
 *   - [5, 9]: we need to calculate x - 5 to calculate x mod 5.
 *   - [9, 14]: we need to calculate x - 10 (or twice x - 5) for the reduction.
 *
 * Bucket membership can be derived through `sec_leq_8x32`. This should not
 * leak the actual value x modulo 5, which is still uniformly distributed in
 * the interval [0, 4]. The subtraction is calculated with `sec_add_8x32`.
 *
 * CAUTION: This is a hack and not a peer-reviewed gadget. It can be used to
 * calculate the modulo 5 step of the `CoeffFromHalfByte` function (Algorithm
 * 15) of FIPS-204.
 *
 * @param[in]  w0: x0_B, 8 Boolean-shared coefficients in [0, 14] (share 0).
 * @param[in]  w1: x1_B, 8 Boolean-shared coefficients in [0, 14] (share 1).
 * @param[out] w0: y0_B, 8 Boolean-shared coefficients x mod 5 (share 0).
 * @param[out] w1: y1_B, 8 Boolean-shared coefficients x mod 5 (share 1).
 */
sec_mod5_8x32:
  /* Save x0_B and x1_B. */
  bn.mov w4, w0
  bn.xor w31, w31, w31 /* dummy */
  bn.mov w5, w1

  /* w6 = [5, 5, 5, 5, 5, 5, 5, 5]. */
  bn.addi w6, w31, 5
  bn.or w6, w6, w6 << 32
  bn.or w6, w6, w6 << 64
  bn.or w6, w6, w6 << 128

  /*
   * Evaluate x <= 9.
   */

  /* w2 = [9, 9, 9, 9, 9, 9, 9, 9]. */
  bn.addi w2, w31, 9
  bn.or w2, w2, w2 << 32
  bn.or w2, w2, w2 << 64
  bn.or w2, w2, w2 << 128

  jal x1, sec_leq_8x32

  /* w7[i] = 5 if x[i] > 9, else 0. */
  bn.not w0, w0
  bn.and w7, w0, w6

  /*
   * Evaluate x <= 4.
   */

  bn.mov w0, w4

  /* w2 = [4, 4, 4, 4, 4, 4, 4, 4]. */
  bn.addi w2, w31, 4
  bn.or w2, w2, w2 << 32
  bn.or w2, w2, w2 << 64
  bn.or w2, w2, w2 << 128

  bn.mov w1, w5
  jal x1, sec_leq_8x32

  /* w8[i] = 5 if x[i] > 4, else 0. */
  bn.not w0, w0
  bn.and w8, w0, w6

  /* w7[i] = -10 if x[i] > 9, -5 if (x[i] > 4 and x[i] < 10), else 0. */
  bn.addv.8s w7, w7, w8
  bn.subv.8s w7, w31, w7

  /* y = x - w7. */
  bn.mov w0, w4
  bn.mov w2, w7 /* prevent accessing shares in successive instructions */
  bn.mov w1, w5
  bn.mov w3, w31
  jal x1, sec_add_8x32

  ret

.data
.balign 32

/* GAMMA2 = (Q - 1) / 32. */
_sec_decompose_gamma2:
.word 0x0003ff00
.word 0x0003ff00
.word 0x0003ff00
.word 0x0003ff00
.word 0x0003ff00
.word 0x0003ff00
.word 0x0003ff00
.word 0x0003ff00

_sec_decompose_alphas:
.word 0x0007fe00 /* ALPHA = 2 * GAMMA1 = (Q - 1) / 16 */
.word 0x007f0009 /* ALPHA^-1 * 2^32 mod Q (Montgomery domain) */
.zero 24 /* Padding */
