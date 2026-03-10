/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Polynomial sampling routines. */

.globl rej_ntt_poly

.text

/**
 * Rejection sample a polynomial in the NTT domain.
 *
 * This routine implements the `RejNTTPoly` function (Algorithm 30) of FIPS-204
 * and samples a polynomial directly in the NTT domain with coefficients in the
 * interval [0, Q - 1].
 *
 * @param[in] x2: DMEM output location of sampled polynomial.
 * @param[in] x3: DMEM location of rho (34 bytes), 64 bytes allocated region.
 */
rej_ntt_poly:
  /* Push clobbered registers onto the stack. */
  .irp reg, x2, x4, x5, x6, x7, x8, x9, x10
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* (Q - 1)^8 = (0x007fe000, 0x007fe000, ..., 0x007fe000). */
  bn.not w5, w31
  bn.shv.8s w4, w5 >> 22
  bn.shv.8s w4, w4 << 13

  /* (2^23 - 1)^8 = (0x007fffff, 0x007fffff, ..., 0x007fffff). */
  bn.shv.8s w5, w5 >> 9

  /* Initialize the SHAKE128 XOF and absorb the 34 bytes of RHO. */
  jal x1, xof_shake128_init
  addi x20, x0, 34
  addi x21, x3, 0
  addi x22, x0, 0
  jal x1, xof_absorb
  jal x1, xof_process

  /*
   * Part 1: Sample (without rejections) a full 256-coefficient polynomial with
   * coefficients in the interval [0, 2^23 - 1]. The probability that this
   * polynomial does not contain any coefficients that are >= Q is ~78%, hence
   * on average only roughly every 4th polynomial needs to be corrected.
   */

  addi x4, x2, 0

  /* Sample 256 coefficients in the interval [0, 2^23 - 1]. */
  loopi 32, 7
    /* Squeeze 24 bytes from the XOF, enough to populate one 8-coefficient
       WDR. */
    jal x1, xof_squeeze24
    bn.xor w8, w29, w30 /* unmask */

    loopi 8, 2
      bn.rshi w0, w8, w0 >> 32
      bn.rshi w8, w31, w8 >> 24
      /* End of loop */

    /* Set bits 31:23 to 0 to map the 3-byte value to [0, 2^23 - 1]. */
    bn.and w0, w0, w5
    bn.sid x0, 0(x4++)
    /* End of loop */

  /*
   * Part 2: Check and possibly correct the sampled polynomial. Every
   * coefficient x[i] >= Q will be discarded and all the coefficients x[j] for
   * i <= j < 255 will be shifted one position such that x[j] = x[j + 1] and
   * the last coefficient x[255] is squeezed from the XOF.
   */

  /* Index of coefficient to be checked, in reverse order. */
  addi x4, x0, 255 /* counter */

  /* Number of 3-byte squeezes remaining in the buffer. */
  addi x5, x0, 0 /* squeeze */

  /* Q - 1. */
  li x6, 8380416

  /* Iterate over the entire polynomial and check for coefficients that are
     >= Q. 8 coefficients in parallel per iteration. */
  loopi 32, 10
    bn.lid x0, 0(x2)

    /* w0 = 0, if all coefficients are in the interval [0, Q - 1]. */
    bn.sub w0, w4, w0
    bn.shv.8s w0, w0 >> 31

    /* If an invalid coefficient has been detected correct the vector of 8
       coefficients. */
    bn.cmp w0, w31, FG0
    csrrs x7, FG0, x0
    andi x7, x7, 8
    bne x7, x0, _rej_ntt_poly_advance

    jal x1, _rej_ntt_poly_correct

    /* The vector of 8 coefficients has either been valid or been corrected,
       we advance to the next 8 coefficients and adjust the coefficient index. */
_rej_ntt_poly_advance:
    addi x2, x2, 32
    addi x4, x4, -8
    /* End of loop */

  jal x1, xof_finish

  /* Restore clobbered general-purpose registers. */
  .irp reg, x10, x9, x8, x7, x6, x5, x4, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret

/* Correct a vector of 8 coefficients that contains at least one invalid
   value. */
_rej_ntt_poly_correct:
  /* Copy coefficient address and index. */
  addi x7, x2, 0
  addi x8, x4, 0

  /* Iterate over all eight coefficients to find the invalid values and correct
     them. */
  loopi 8, 8
_rej_ntt_poly_correct_loop_start:
    /* Check that that coefficient X[i] < Q and discard it if is not by
       shifting all the following coefficients by one position. */
    lw x9, 0(x7)
    sub x9, x6, x9
    srai x9, x9, 31
    beq x9, x0, _rej_ntt_poly_correct_loop_end

    jal x1, _rej_ntt_poly_shift_right

    /* Having corrected the bad coefficient restart at the top. */
    jal x0, _rej_ntt_poly_correct_loop_start

    /* A coefficient is either valid or has been corrected, advance to the next
       one. */
_rej_ntt_poly_correct_loop_end:
    addi x7, x7, 4
    addi x8, x8, -1
    /* End of loop */

  ret

/* Given an index 0 <= i < 256, shift all the coefficients X[j] one position
   to the right such that X[j] = X[j+1] for i <= j < 255 and set X[255] to
   the output of the XOF. */
_rej_ntt_poly_shift_right:
  /* Copy coefficient address. */
  addi x10, x7, 0

  /* If the coefficient pointer is 0, we have reached the last coefficient
     which is replaced by the XOF output. */
  beq x8, x0, _rej_ntt_poly_shift_right_last_coeff

  /* Shifting loop. Set X[j] = X[j+1] for i <= j < 255. */
  loop x8, 3
    lw x9, 4(x10)
    sw x9, 0(x10)
    addi x10, x10, 4
    /* End of loop */

/* X[255] is set to the output of the XOF. */
_rej_ntt_poly_shift_right_last_coeff:
  /* If the buffer is empty recharge it. */
  bne x5, x0, _rej_ntt_poly_shift_right_recharge_skip

  jal x1, xof_squeeze24
  bn.xor w8, w29, w30 /* unmask */
  addi x5, x0, 8

_rej_ntt_poly_shift_right_recharge_skip:
  /* Pointer to X[248]. */
  addi x10, x10, -28

  bn.lid x0, 0(x10)

  /* Shift in 3 bytes from the XOF. */
  bn.rshi w0, w0, w31 >> 224
  bn.rshi w0, w8, w0 >> 24
  bn.rshi w0, w31, w0 >> 8
  bn.and w0, w0, w5 /* Set bit 23 to 0. */

  bn.sid x0, 0(x10)

  /* Update the XOF buffer and capacity. */
  bn.rshi w8, w31, w8 >> 24
  addi x5, x5, -1

  ret
