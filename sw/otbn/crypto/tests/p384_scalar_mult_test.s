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

p384_scalar_mult_test:

  /* Init all-zero register. */
  bn.xor  w31, w31, w31

  /* call scalar point multiplication routine in P-384 lib */
  jal      x1, p384_scalar_mult

  /* load result to WDRs for comparison with reference */
  li        x2, 0
  la        x3, x
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)
  la        x3, y
  bn.lid    x2++, 0(x3)
  bn.lid    x2, 32(x3)

  /* load domain parameter p (modulus)
     [w13, w12] = p = dmem[p384_p] */
  li        x2, 12
  la        x3, p384_p
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* unmask x coordinate x = x_m + m mod p = x-coord. + y-coord. mod p */
  bn.add    w0, w0, w2
  bn.addc   w1, w1, w3

  bn.mov    w18, w0
  bn.mov    w19, w1
  bn.mov    w20, w31
  jal       x1, p384_reduce_p
  bn.mov    w0, w16
  bn.mov    w1, w17

  ecall
