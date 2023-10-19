/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.globl p256_isoncurve

/**
 * Checks if a point is a valid curve point on curve P-256 (secp256r1)
 *
 * Returns rhs = x^3 + ax + b  mod p
 *     and lhs = y^2  mod p
 *         with x,y being the affine coordinates of the curve point
 *              a, b and p being the domain parameters of P-256
 *
 * This routine checks if a point with given x- and y-coordinate is a valid
 * curve point on P-256.
 * The routine checks whether the coordinates are a solution of the
 * Weierstrass equation y^2 = x^3 + ax + b  mod p.
 * The routine makes use of the property that the domain parameter 'a' can be
 * written as a=-3 for the P-256 curve, hence the routine is limited to P-256.
 * The routine does not return a boolean result but computes the left side
 * and the right sight of the Weierstrass equation and leaves the final
 * comparison to the caller.
 * The routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]      w31: all-zero
 * @param[in]  dmem[x]: affine x-coordinate of input point
 * @param[in]  dmem[y]: affine y-coordinate of input point
 * @param[out]     w18: lhs, left side of equation = (x^3 + ax + b) mod p
 * @param[out]     w19: rhs, right side of equation = y^2 mod p
 *
 * clobbered registers: x2, x3, x19, x20, w0, w19 to w29
 * clobbered flag groups: FG0
 */
p256_isoncurve:
  /* Set up for coordinate arithmetic.
       MOD <= p
       w28 <= r256
       w29 <= r448 */
  jal       x1, setup_modp

  /* load domain parameter b from dmem
     w27 <= b = dmem[p256_b] */
  li        x2, 27
  la        x3, p256_b
  bn.lid    x2, 0(x3)

  /* load affine x-coordinate of curve point from dmem
     w26 <= dmem[x] */
  la        x3, x
  li        x2, 26
  bn.lid    x2, 0(x3)

  /* w19 <= x^2 = w26*w26 */
  bn.mov    w25, w26
  bn.mov    w24, w26
  jal       x1, mul_modp

  /* w19 = x^3 <= x^2 * x = w25*w24 = w26*w19 */
  bn.mov    w25, w19
  bn.mov    w24, w26
  jal       x1, mul_modp

  /* for curve P-256, 'a' can be written as a = -3, therefore we subtract
     x three times from x^3.
     w19 = x^3 + ax <= x^3 - 3x  mod p */
  bn.subm   w19, w19, w26
  bn.subm   w19, w19, w26
  bn.subm   w19, w19, w26

  /* w18 <= x^3 + ax + b mod p = w19 + w27 mod p = lhs */
  bn.addm   w18, w19, w27

  /* Load affine y-coordinate of curve point from dmem
     w26 <= dmem[y] */
  la        x3, y
  li        x2, 24
  bn.lid    x2, 0(x3)

  /* w19 <= w24*w24 mod p = y^2 mod p = rhs */
  bn.mov    w25, w24
  jal       x1, mul_modp

  ret
