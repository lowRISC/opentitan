/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Polynomial rounding routines for ML-DSA-87 keygen. */

.globl power2round

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
