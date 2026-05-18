/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Polynomial sampling routines for ML-DSA-87 keygen. */

.globl rej_bounded_poly

.text

/**
 * Rejection sample a polynomial with coefficients in the interval [-ETA, ETA].
 *
 * This routine can be used to sample a secret-key polynomial S as part of the
 * vectors S1 and S2 whose coefficients are uniformly distributed in the
 * interval [-ETA, ETA] for ETA = 2. This is a direct implementation of the
 * `RejBoundedPoly` function (Algorithm 31) of FIPS-204.
 *
 * Note that although the seed rho is a 66-byte Boolean-shared value it shall
 * be provided in two 96-byte allocated regions in DMEM for seamless
 * processing by the XOF.
 *
 * @param[in] x2: DMEM address of the first Boolean share of rho.
 * @param[in] x3: DMEM address of the second Boolean share of rho.
 * @param[in] x4: DMEM address of the first arithmetic share of the sampled S.
 * @param[in] x5: DMEM address of the second arithmetic share of the sampled S.
 */
rej_bounded_poly:
  /* Push clobbered general-purpose registers onto the stack. */
  .irp reg, x4, x5, x6, x7, x8, x9
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* Load [ETA, ETA, ..., ETA] into w16. */
  bn.not w16, w31
  bn.shv.8s w16, w16 >> 31
  bn.shv.8s w16, w16 << 1

  /* Set the rejection bound to 14. */
  bn.addi w17, w31, 14

  /* Prepare a 32-bit mask. w12 = 0x000...000ffffffff. */
  bn.not w12, w31
  bn.rshi w12, w31, w12 >> 224

  /* Prepare a 4-bit mask. w13 = 0xfff...fff0000000f. */
  bn.not w13, w31
  bn.rshi w13, w13, w31 >> 224
  bn.addi w13, w13, 15

  /* Initialize the SHAKE256 XOF and absorb the 66 bytes of rho. */
  jal x1, xof_shake256_init
  addi x20, x0, 66
  addi x21, x2, 0
  addi x22, x3, 0
  jal x1, xof_absorb
  jal x1, xof_process

  /* Number of half-byte words left in the buffer. */
  addi x6, x0, 0

  /* WDR pointers. */
  addi x7, x0, 0
  addi x8, x0, 1

  /*
   * The following loop unfolds in two parts. First, rejection sample a
   * Boolean shared vector x consisting of 8 4-bit coefficients in the interval
   * [0, 14]. Second, compute x mod 5 and convert the coefficients to
   * arithmetic shares. Repeat this 32 times until all the coefficients of the
   * polynomial have been sampled.
   */
  loopi 32, 42

    /* Initialize the WDRs that hold intermediate results with randomness. */
    bn.wsrr w4, URND
    bn.wsrr w5, URND
    bn.wsrr w10, URND
    bn.wsrr w11, URND

    loopi 8, 27
     /* If the squeezed buffer is empty re-squeeze a new batch of 64 4-bit
        coefficients. */
_rej_bounded_poly_squeeze_start:
      bne x6, x0, _rej_bounded_poly_squeeze_end

      /* Squeeze and reset the counter. */
      jal x1, xof_squeeze32
      addi x6, x0, 64

      /* Rejection loop. Check if a 4-bit value is in interval [0, 14], if so
         keep it otherwise try the next 4-bit value. */
_rej_bounded_poly_squeeze_end:
      /* Update the buffer capacity. */
      addi x6, x6, -1

      /* Extract a Boolean-shared 4-bit value x[i] from the XOF buffers
         (w29, w30) and place it at the LSB in w0 and w1. */

      /* Randomness to shift into registers when a coefficient is extracted.
         This avoids that few secrets bits are isolated in an all-zero WDR. */
      bn.wsrr w6, URND
      bn.wsrr w7, URND

      /*
       * Share 0:
       */

      /* Extract 4 bits from the buffer and place at the LSB of w4. */
      bn.rshi w4, w29, w4 >> 4
      bn.rshi w4, w6, w4 >> 252

      /* Mask out the lower 4 bits. This is necessary for the correctness of
         the `sec_leq_8x32` bound check below. */
      bn.and w4, w4, w13

      /* Remove the extracted 4 bits from the buffer. */
      bn.rshi w29, w6, w29 >> 4

      bn.xor w31, w31, w31 /* dummy */

      /*
       * Share 1:
       */

      /* Extract 4 bits from the buffer and place at the LSB of w5. */
      bn.rshi w5, w30, w5 >> 4
      bn.rshi w5, w7, w5 >> 252

      /* Mask out the lower 4 bits. This is necessary for the correctness of
         the `sec_leq_8x32` bound check below. */
      bn.and w5, w5, w13

      /* Remove the extracted 4 bits from the buffer. */
      bn.rshi w30, w7, w30 >> 4

      /* Check that x[i] <= 14. */
      bn.mov w0, w4
      bn.mov w2, w17 /* splice */
      bn.mov w1, w5
      jal x1, sec_leq_8x32

      /* We are only interested in the lower 32 bits of the `sec_leq_8x32`
         result, mask them out here. */
      bn.and w0, w0, w12

      /* If x[i] > 14, then x9 = 1, else x9 = 0. */
      bn.cmp w0, w31, FG0
      csrrs x9, FG0, x0
      andi x9, x9, 0x8
      bne x9, x0, _rej_bounded_poly_squeeze_start

      /* x[i] has passed the rejection check and can be shifted into w10 and
         w11. */
      bn.rshi w10, w4, w10 >> 32
      bn.xor w31, w31, w31 /* dummy */
      bn.rshi w11, w5, w11 >> 32
      /* End of loop */

    /*
     * At this point, we have a Boolean-shared vector x with 8 uniformly
     * distributed coefficients in the interval [0, 14]. First calculate
     * x = x mod 5, then convert them to arithmetic shares and calculate
     * x = 2 - x mod Q. This part is an implementation of the
     * `CoeffFromHalfByte` function (Algorithm 15) of FIPS-204.
     */

    /* Compute x mod 5 and convert to arithmetic shares. */
    bn.mov w0, w10
    bn.xor w31, w31, w31 /* dummy */
    bn.mov w1, w11

    jal x1, sec_mod5_8x32
    jal x1, sec_b2a_8x32

    /* Compute 2 - x mod Q and store the vector in the output DMEM location. */
    bn.subvm.8S w0, w16, w0
    bn.sid x7, 0(x4++)

    bn.xor w31, w31, w31 /* dummy */

    bn.subvm.8S w1, w31, w1
    bn.sid x8, 0(x5++)
    /* End of loop */

  jal x1, xof_finish

  /* Restore clobbered general-purpose registers. */
  .irp reg, x9, x8, x7, x6, x5, x4
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret
