/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Polynomial encoding/decoding routines for ML-DSA-87 keygen. */

.globl encode_t0

.text

/**
 * Encode a T0 polynomial into a dense representation.
 *
 * A T0 of the secret key consists of 256 13-bit coefficients in the range
 * ]-2^12, 2^12] hence its encoded representation has a size of
 * 256 * 13 = 3328 bits or 416 bytes. This routine is a part of the `skEncode`
 * function (Algorithm 24) of FIPS-204.
 *
 * @param[in] x2: DMEM location of the decoded T0 polynomial.
 * @param[in] x3: DMEM location of the encoded T0 polynomial.
 */
encode_t0:
  /* Push clobbered registers onto the stack. */
  .irp reg, x2, x3, x4
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* Prepare subtraction vector w2 = b = (2^12, 2^12, ..., 2^12). */
  bn.not w1, w31
  bn.shv.8s w1, w1 >> 31
  bn.shv.8s w1, w1 << 12

  /*
   * We have 3328 = 13 * 256, hence all 256 13-bit coefficients exactly fit in
   * 13 WDRs. Iterate in chunks of 8 coefficients over the polynomial and shift
   * each coefficient into w2-w14 to form the encoded representation.
   */

  loopi 32, 18
    /* Load 8 coefficients into w0. */
    bn.lid x0, 0(x2++)

    /* Compute b - x mod Q for each coefficient x in w0. This is the centering
       step of the `BitPack` function (Algorithm 17) of FIPS-204. */
    bn.subvm.8S w0, w1, w0

    loopi 8, 14
      /* Shift each 13-bit coefficient into w2-w14. */
      bn.rshi w2, w3, w2 >> 13
      bn.rshi w3, w4, w3 >> 13
      bn.rshi w4, w5, w4 >> 13
      bn.rshi w5, w6, w5 >> 13
      bn.rshi w6, w7, w6 >> 13
      bn.rshi w7, w8, w7 >> 13
      bn.rshi w8, w9, w8 >> 13
      bn.rshi w9, w10, w9 >> 13
      bn.rshi w10, w11, w10 >> 13
      bn.rshi w11, w12, w11 >> 13
      bn.rshi w12, w13, w12 >> 13
      bn.rshi w13, w14, w13 >> 13
      bn.rshi w14, w0, w14 >> 13

      /* Remove the coefficient from w0. */
      bn.rshi w0, w31, w0 >> 32
      /* End of loop */
    nop
    /* End of loop */

  /* Store the encoded polynomial in w2-w14 to DMEM. */
  addi x4, x0, 2
  loopi 13, 2
    bn.sid x4++, 0(x3)
    addi x3, x3, 32
    /* End of loop */

  /* Restore clobbered general-purpose registers. */
  .irp reg, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret
