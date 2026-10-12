/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.include "mldsa87.inc"

/* Polynomial rounding and norm check routines. */

/* Keygen */
.globl power2round

/* Verify */
.globl shift_left
.globl decompose
.globl check_infinity_norm

/* Polynomial rounding routines for ML-DSA-87 keygen. */

.text

/**
 * Round a polynomial T into lower-bit and higher-bit polynomials T0 and T1.
 *
 * Given a coefficient t of T in [0, Q - 1], this routine decomposes t into a
 * lower-bit part t0 and a higher-bit part t1 such that t1 * 2^D + t0 mod Q = x
 * with t0 in ]-2^(D-1), 2^(D-1)] and D = 13. This is an implementation of the
 * `power2round` function (Algorithm 35) of FIPS-204.
 *
 * @param[in] x2: DMEM address of the T polynomial.
 * @param[in] x3: DMEM address of the lower-bits T0 polynomial.
 * @param[in] x4: DMEM address of the higher-bits T1 polynomial.
 */
power2round:
  /* Push clobbered registers onto the stack. */
  .irp reg, x2, x3, x4, x5, x6
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* Prepare an offset vector w3 = (2^(D-1) - 1, ..., 2^(D-1) - 1). */
  bn.not w3, w31
  bn.shv.8s w3, w3 >> 20

  /* WDR pointers. */
  addi x5, x0, 0
  addi x6, x0, 1

  /*
   * The rounding operation functions as follows, given a coefficient t in
   * [0, Q - 1]:
   *
   * t1 = (t + (2^(D-1) - 1)) / 2^D
   * t0 = (t - t1 * 2^D) mod Q
   *
   * The derivation of t0 is straightforward and follows directly from the
   * definition of the operation t1 * 2^D + t0 mod Q. The tricky part is the
   * calculation of t1.
   *
   * First, note that if the offset is not added to t before dividing by 2^D,
   * we would arrive at a t0 value in [0, 2^D - 1], however we need t0 to be
   * centered in the interval ]2^(D-1), 2^(D-1)]. We distinguish two cases:
   *
   *  1. t0 <= 2^(D-1): t0 is already in the correct interval. The addition
   *     t0 + (2^(D-1) - 1) will not cause a carry bit in t1.
   *
   *  2. t0 > 2^(D-1): The addition t0 + (2^(D-1) - 1) causes a carry in t1,
   *     hence the subtraction t0 = (t - t1 * 2^D) will be in the interval
   *     ]2^(D-1), -1].
   */

  loopi 32, 7
    /* Load a vector of 8 coefficients t into w0. */
    bn.lid x5, 0(x2++)

    /* t1 = (t + (2^(D-1) - 1)) / 2^D. */
    bn.addv.8S w1, w0, w3
    bn.shv.8S w1, w1 >> 13

    /* t0 = (t - t1 * 2^D) mod Q. */
    bn.shv.8S w2, w1 << 13
    bn.subvm.8S w0, w0, w2

    /* Store both vectors t0 and t1 back to DMEM. */
    bn.sid x5, 0(x3++)
    bn.sid x6, 0(x4++)
    /* End of loop */

  /* Restore clobbered general-purpose registers. */
  .irp reg, x6, x5, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret

/* Various finite-field rounding routines. */

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
  la x6, mldsa87_const_decompose_alphas
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
 * Decomposition constants (declared in `mldsa87_mem.s`).
 */

mldsa87_const_decompose_alphas:
.word 0x0007fe00 /* ALPHA = 2 * GAMMA1 = (Q - 1) / 16 */
.word 0x007f0009 /* ALPHA^-1 * 2^32 mod Q (Montgomery domain) */
.zero 24 /* Padding */

/* GAMMA2 = (Q - 1) / 32. */
mldsa87_const_decompose_gamma2:
.word 0x0003ff00
.word 0x0003ff00
.word 0x0003ff00
.word 0x0003ff00
.word 0x0003ff00
.word 0x0003ff00
.word 0x0003ff00
.word 0x0003ff00

/* ML-DSA modulus: Q = 8380417. */
mldsa87_const_decompose_q:
.word 0x007fe001
.word 0x007fe001
.word 0x007fe001
.word 0x007fe001
.word 0x007fe001
.word 0x007fe001
.word 0x007fe001
.word 0x007fe001

/* Unmasked infinity norm bound check. */

.text

/**
 * Check the infinity norm of a polynomial against a bound b.
 *
 * The infinity norm of a polynomial |X|_inf is defined as max_i
 * |X[i] mod^+- q|. This routine sets w0 = 2^256-1 if |X|_inf < b, else w0 = 0.
 *
 * The bound b is assumed to be provided in a 8-element vectorized form.
 *
 * @param[in] x2: DMEM address of the input polynomial X.
 * @param[in] x3: DMEM address of the bound vector b.
 * @param[out]: w0: 2^256-1 if |x|_inf < b, else w0 = 0.
 */
check_infinity_norm:
  /* Push clobbered registers onto the stack. */
  .irp reg, x2, x4
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /*
    For the sake of simplicity, let us start with a weaker notion of the bound
    check. A coefficient x of a polynomial is within bounds in the unreduced
    representation if |x mod^+- Q| <= b. In other words, if either x <= b or
    x => (Q - b) is the case as shown below where the 'v' marks the valid
    intervals and 'i' the invalid one.

                | vvvvvvv | iiiiiiiiiiiiiiiii | vvvvvvv |
                ^         ^                   ^         ^
                0         b                 Q - b       Q

    To simplify this check, we first compute x + b mod Q which will shift the
    valid intervals into a continuous range such that

                | vvvvvvv | vvvvvvv | iiiiiiiiiiiiiiiii |
                ^         ^         ^                   ^
                0         b       2 * b                 Q

    Now all that is left is to verify x <= 2 * b, which we can do by adding the
    value x + b mod Q to 2^31 - 1 - (2 * b) and check whether the MSB is set
    or not. It is not set if and only if |x mod^+- Q| <= b. All the infinity
    norm checks in ML-DSA are strict inequalities, hence we need to execute the
    above algorithm on the bounds b - 1.
  */

  /* Load the bound constant and subtract 1 from it. */
  addi x4, x0, 2
  bn.lid x4, 0(x3)

  bn.not w0, w31
  bn.shv.8s w0, w0 >> 31
  bn.subv.8s w2, w2, w0

  /* b' = 2 * (b - 1). */
  bn.addv.8S w3, w2, w2

  /* 2^31 - 1 - b'. */
  bn.not w4, w31
  bn.shv.8s w4, w4 >> 1
  bn.subv.8S w4, w4, w3

  /* Flag, 0 if and only if |X[i]|_inf < b for 0 <= i < 256. */
  bn.xor w1, w1, w1

  /* Iterate over the entire polynomial in chunks of 8 coefficients and check
     their infinity norm in parallel. */
  loopi 32, 5
    bn.lid x0, 0(x2++)

    /* x = X[i] + (b - 1) mod Q. */
    bn.addvm.8S w0, w0, w2
    /* (2^31 - 1 - (2 * (b - 1)) + x. */
    bn.addv.8S w0, w0, w4
    /* Isolate the MSB. */
    bn.shv.8S w0, w0 >> 31

    /* If the MSB is 0, then the 8 coefficients have passed the bound check. */
    bn.or w1, w1, w0
    /* End of loop */

  /* Set w0 = 2^256-1 if |X[i] mod^+- Q| < b for all 0 <= i < 256. */
  bn.subi w0, w31, 1
  bn.cmp w1, w31, FG0
  bn.sel w0, w0, w31, FG0.Z

  /* Restore clobbered general-purpose registers. */
  .irp reg, x4, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret
