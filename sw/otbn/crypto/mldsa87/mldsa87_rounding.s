/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Various finite-field rounding routines. */

.globl shift_left

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
