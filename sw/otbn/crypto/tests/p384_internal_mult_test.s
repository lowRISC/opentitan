/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for P-384 scalar multiplication
 *
 * Performs multiplication of a P-384 curve point by a scalar. Both, the
 * scalar and the affine coordinates of the point are contained in the
 * .data section below.
 *
 * See comment at the end of the file for expected values of coordinates
 * of resulting point.
 */

.section .text.start

p384_internal_mult_test:

  /* Init all-zero register. */
  bn.xor  w31, w31, w31

  /* set dmem pointer to domain parameter b */
  la        x28, p384_b

  /* set dmem pointer to scratchpad */
  la        x30, scratchpad

  /* set dmem pointer to point to x-coordinate */
  la       x20, x

  /* set dmem pointer to point to y-coordinate */
  la       x21, y

  /* set dmem pointer to point to 1st scalar share d0 */
  la       x17, d0

  /* set dmem pointer to point to 2nd scalar share d1 */
  la       x19, d1

  /* load domain parameter p (modulus)
     [w13, w12] = p = dmem[p384_p] */
  li        x2, 12
  la        x3, p384_p
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* load domain parameter n (order of base point)
     [w11, w10] = n = dmem[p384_n] */
  li        x2, 10
  la        x3, p384_n
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* call scalar point multiplication routine in P-384 lib */
  jal      x1, scalar_mult_int_p384

  ecall
