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

  /* load domain parameter p (modulus)
     [w13, w12] = p = dmem[p384_p] */
  li        x2, 12
  la        x3, p384_p
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* load masked x-coordinate and its mask for unmasking
     [w1, w0] <= dmem[ecdh_x0] = x_m
     [w3, w2] <= dmem[ecdh_x1] = r_x */
  li        x2, 0
  la        x3, ecdh_x0
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)
  la        x3, ecdh_x1
  bn.lid    x2++, 0(x3)
  bn.lid    x2, 32(x3)

  /* unmask x coordinate x = x_m + r_x mod p
     [w1, w0] <= ([w1, w0] + [w3, w2]) mod p */
  bn.add    w18, w0, w2
  bn.addc   w19, w1, w3
  bn.mov    w20, w31
  jal       x1, p384_reduce_p
  bn.mov    w0, w16
  bn.mov    w1, w17

  /* load masked y-coordinate and its mask for unmasking
     [w5, w4] <= dmem[ecdh_y0] = y_m
     [w7, w6] <= dmem[ecdh_y1] = r_y */
  li        x2, 4
  la        x3, ecdh_y0
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)
  la        x3, ecdh_y1
  bn.lid    x2++, 0(x3)
  bn.lid    x2, 32(x3)

  /* unmask y coordinate y = y_m + r_y mod p
     [w3, w2] <= ([w5, w4] + [w7, w6]) mod p */
  bn.add    w18, w4, w6
  bn.addc   w19, w5, w7
  bn.mov    w20, w31
  jal       x1, p384_reduce_p
  bn.mov    w2, w16
  bn.mov    w3, w17

  ecall
