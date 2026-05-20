/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Polynomial encoding/decoding routines for ML-DSA-87 keygen. */

.globl encode_t0
.globl encode_t1
.globl encode_s

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

/**
 * Encode a T1 polynomial into a dense representation.
 *
 * A T1 of the public key consists of 256 10-bit coefficients in the range
 * [0, 2^10-1] hence its encoded representation has a size of 256 * 10 = 2560
 * bits or 320 bytes. This routine is a part of the `pkEncode` function
 * (Algorithm 22) of FIPS-204.
 *
 * @param[in] x2: DMEM location of the decoded T1 polynomial.
 * @param[in] x3: DMEM location of the encoded T1 polynomial.
 */
encode_t1:
  /* Push clobbered registers onto the stack. */
  .irp reg, x2, x3, x4
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /*
   * We have 2560 = 10 * 256, hence all 256 10-bit coefficients exactly fit in
   * 10 WDRs. Iterate in chunks of 8 coefficients over the polynomial and shift
   * each coefficient into w1-w10 to form the encoded representation.
   */

  loopi 32, 14
    /* Load 8 coefficients into w0. */
    bn.lid x0, 0(x2++)

    loopi 8, 11
      /* Shift each 10-bit coefficient into w1-w10. */
      bn.rshi w1, w2, w1 >> 10
      bn.rshi w2, w3, w2 >> 10
      bn.rshi w3, w4, w3 >> 10
      bn.rshi w4, w5, w4 >> 10
      bn.rshi w5, w6, w5 >> 10
      bn.rshi w6, w7, w6 >> 10
      bn.rshi w7, w8, w7 >> 10
      bn.rshi w8, w9, w8 >> 10
      bn.rshi w9, w10, w9 >> 10
      bn.rshi w10, w0, w10 >> 10

      /* Remove the coefficient from w0. */
      bn.rshi w0, w31, w0 >> 32
      /* End of loop */
    nop
    /* End of loop */

  /* Store the encoded polynomial in w1-w10 to DMEM. */
  addi x4, x0, 1
  loopi 10, 2
    bn.sid x4++, 0(x3)
    addi x3, x3, 32
    /* End of loop */

  /* Restore clobbered general-purpose registers. */
  .irp reg, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret

/**
 * Encode a S{1, 2} polynomial to a dense representation.
 *
 * A S{1, 2} polynomial of the secret key consists of 256 3-bit coefficients in
 * the range [-ETA, ETA] for ETA = 2, hence its encoded representation has a
 * size of 256 * 3 = 768 bits or 96 bytes. This routine is a part of the
 * `skEncode` function (Algorithm 24) of FIPS-204.
 *
 * The S polynomial is assumed to be passed as two arithmetic shares. The
 * encoded polynomial is returned as two Boolean shares.
 *
 * @param[in] x2: DMEM address of the first arithmetic share of S.
 * @param[in] x3: DMEM address of the second arithmetic share of S.
 * @param[in] x4: DMEM address of the first Boolean share of the encoded S.
 * @param[in] x5: DMEM address of the second Boolean share of the encoded S.
 */
encode_s:
  /* Push clobbered registers onto the stack. */
  .irp reg, x2, x3, x6, x7
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* Set up subtraction vector w2 = [ETA, ETA, ..., ETA]. */
  bn.not w2, w31
  bn.shv.8s w2, w2 >> 31
  bn.shv.8s w2, w2 << 1

  /* WDR pointers. */
  addi x6, x0, 0
  addi x7, x0, 1

  /* Initialize the registers that hold the compressed polynomial shares with
     randomness. This avoids isolating secrets bits in an all-zero register
     during the shifting operations. */

  /* Share 0. */
  bn.wsrr w3, URND
  bn.wsrr w4, URND
  bn.wsrr w5, URND
  /* Share 1. */
  bn.wsrr w6, URND
  bn.wsrr w7, URND
  bn.wsrr w8, URND

  /* Encode the polynomial in chunks of 8 coefficients at a time. */
  loopi 32, 19
    /* Load the two arithmetically shared vectors of 8 coefficients
       x = (x0, x1) and compute ETA - x mod Q. This is the centering step of
       the `BitPack` function (Algorithm 17) of FIPS-204. */

    /* Share 0. */
    bn.lid x6, 0(x2++)
    bn.subvm.8S w0, w2, w0

    bn.xor w31, w31, w31 /* dummy */

    /* Share 1. */
    bn.lid x7, 0(x3++)
    bn.subvm.8S w1, w31, w1

    /* Convert the two arithmetically shared vectors to Boolean shares. */
    jal x1, sec_a2b_8x32

    loopi 8, 11
      /* Randomness to shift into registers when a coefficient is extracted.
         This avoids that few secrets bits are isolated in an all-zero WDR. */
      bn.wsrr w9, URND
      bn.wsrr w10, URND

      /* Share 0: */

      /* Shift a 3-bit coefficient into w3-w5. */
      bn.rshi w3, w4, w3 >> 3
      bn.rshi w4, w5, w4 >> 3
      bn.rshi w5, w0, w5 >> 3
      bn.rshi w0, w9, w0 >> 32

      /* Share 1. */

      bn.xor w31, w31, w31 /* dummy */

      /* Shift a 3-bit coefficient into w6-w8. */
      bn.rshi w6, w7, w6 >> 3
      bn.rshi w7, w8, w7 >> 3
      bn.rshi w8, w1, w8 >> 3
      bn.rshi w1, w10, w1 >> 32
      /* End of loop */

    nop
    /* End of loop */

  /* Store the encoded polynomial shares to DMEM. */

  /* Share 0. */
  addi x6, x0, 3
  bn.sid x6++, 0(x4)
  bn.sid x6++, 32(x4)
  bn.sid x6++, 64(x4)

  bn.xor w31, w31, w31 /* dummy */

  /* Share 1. */
  bn.sid x6++, 0(x5)
  bn.sid x6++, 32(x5)
  bn.sid x6++, 64(x5)

  /* Restore clobbered general-purpose registers. */
  .irp reg, x7, x6, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret
