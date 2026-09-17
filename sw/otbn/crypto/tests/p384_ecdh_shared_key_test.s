/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone elliptic curve P-384 ECDH shared key generation test
 *
 * Uses OTBN ECC P-384 lib to perform a scalar multiplication with a valid
 * example curve point and an example scalar. Both scalar and coordinates of
 * the curve point are contained in the .data section below.
 * The x and y coordinates of the resulting curve point are masked
 * arithmetically with random values and then converted from an arithmetic
 * to a boolean masking scheme.
 *
 * The results of boolean unmasking of both coordinates are compared with the
 * expected values. In addition, the unmasked point is checked to satisfy the
 * curve equation, i.e. that the x- and y-coordinates belong to each other.
 */

.section .text.start

p384_ecdh_shared_key_test:
  /* init all-zero register */
  bn.xor    w31, w31, w31

  /* fill gpp registers with pointers to relevant variables */
  /*la        x17, k0
  la        x19, k1
  la        x20, x
  la        x21, y

  /* call scalar point multiplication routine in P-384 lib */
  jal       x1, p384_scalar_mult

  /* load the masked x-coordinate and its mask for the a2b conversion
     [w12,w11] <= dmem[ecdh_x0] = x_m
     [w19,w18] <= dmem[ecdh_x1] = r_x */
  li        x2, 11
  la        x3, ecdh_x0
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)
  li        x2, 18
  la        x3, ecdh_x1
  bn.lid    x2++, 0(x3)
  bn.lid    x2, 32(x3)

  /* Load domain parameter.
     [w14,w13] = dmem[p384_p] */
  li        x2, 13
  la        x4, p384_p
  bn.lid    x2++, 0(x4)
  bn.lid    x2++, 32(x4)

  /* Arithmetic to boolean conversion */
  jal       x1, p384_arithmetic_to_boolean_mod

  /* Boolean unmasking of the x-coordinate and store it for the on-curve
     check. The input point is not needed anymore.
     dmem[x] <= [w21,w20] ^ [w19,w18] = x */
  bn.xor    w20, w20, w18
  bn.xor    w21, w21, w19
  li        x2, 20
  la        x3, x
  bn.sid    x2++, 0(x3)
  bn.sid    x2, 32(x3)

  /* load the masked y-coordinate and its mask for the a2b conversion
     [w12,w11] <= dmem[ecdh_y0] = y_m
     [w19,w18] <= dmem[ecdh_y1] = r_y */
  li        x2, 11
  la        x3, ecdh_y0
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)
  li        x2, 18
  la        x3, ecdh_y1
  bn.lid    x2++, 0(x3)
  bn.lid    x2, 32(x3)

  /* Arithmetic to boolean conversion; [w14,w13] still holds p. */
  jal       x1, p384_arithmetic_to_boolean_mod

  /* Boolean unmasking of the y-coordinate.
     dmem[y] <= [w21,w20] ^ [w19,w18] = y */
  bn.xor    w20, w20, w18
  bn.xor    w21, w21, w19
  li        x2, 20
  la        x3, y
  bn.sid    x2++, 0(x3)
  bn.sid    x2, 32(x3)

  /* Check that the unmasked coordinates belong to the same curve point by
     computing both sides of the Weierstrass equation.
     dmem[rhs] <= (x^3 + ax + b) mod p
     dmem[lhs] <= (y^2) mod p */
  li        x2, 12
  la        x4, p384_p
  bn.lid    x2++, 0(x4)
  bn.lid    x2++, 32(x4)
  la        x20, x
  la        x21, y
  la        x22, rhs
  la        x23, lhs
  jal       x1, p384_isoncurve

  /* Load the unmasked coordinates for comparison with the reference.
     [w1,w0] <= dmem[x] = x
     [w3,w2] <= dmem[y] = y */
  li        x2, 0
  la        x3, x
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)
  la        x3, y
  bn.lid    x2++, 0(x3)
  bn.lid    x2, 32(x3)

  ecall
