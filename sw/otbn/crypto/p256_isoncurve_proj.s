/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.globl p256_isoncurve_proj

/**
 * Checks if a projective point is a valid curve point on curve P-256 (secp256r1)
 *
 * Returns rhs = x^3 + axz^2 + bz^3  mod p
 *     and lhs = zy^2  mod p
 *         with x,y,z being the projective coordinates of the curve point
 *              a, b and p being the domain parameters of P-256
 *
 * This routine checks if a point with given projective x- and y-coordinate is
 * a valid curve point on P-256.
 * The routine checks whether the coordinates are a solution of the modified
 * Weierstrass equation zy^2 = x^3 + axz^2 + bz^3  mod p.
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
 * @param[in]  dmem[x]: projective x-coordinate of input point
 * @param[in]  dmem[y]: projective y-coordinate of input point
 * @param[in]  dmem[z]: projective y-coordinate of input point
 * @param[out]     w18: lhs, left side of equation = (x^3 + ax + b) mod p
 * @param[out]     w19: rhs, right side of equation = y^2 mod p
 *
 * clobbered registers: x2, x3, x19, x20, w0, w18 to w29
 * clobbered flag groups: FG0
 */
p256_isoncurve_proj:
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

  /* load projective z-coordinate of curve point from dmem
     w26 <= dmem[z] */
  la        x3, z
  li        x2, 26
  bn.lid    x2, 0(x3)

  /* w19 <= z^2 = w26*w26 */
  bn.mov    w25, w26
  bn.mov    w24, w26
  jal       x1, mul_modp

  /* for curve P-256, 'a' can be written as a = -3, therefore we subtract
     z^2 three times from 0.
     w18 = az^2 <= -3z^2  mod p */
  bn.subm   w18, w31, w19
  bn.subm   w18, w18, w19
  bn.subm   w18, w18, w19

  /* w19 <= bz^2 = w27*w19 */
  bn.mov    w25, w27
  bn.mov    w24, w19
  jal       x1, mul_modp

  /* w19 <= bz^3 = w26*w19 */
  bn.mov    w25, w26
  bn.mov    w24, w19
  jal       x1, mul_modp

  /* Move the modified b back into w27. */
  bn.mov    w27, w19

  /* load projective x-coordinate of curve point from dmem
     w26 <= dmem[x] */
  la        x3, x
  li        x2, 26
  bn.lid    x2, 0(x3)

  /* w19 <= axz^2 = w26*w18 */
  bn.mov    w25, w26
  bn.mov    w24, w18
  jal       x1, mul_modp

  /* Move the modified axz^2 into w18. */
  bn.mov    w18, w19

  /* w19 <= x^2 = w26*w26 */
  bn.mov    w25, w26
  bn.mov    w24, w26
  jal       x1, mul_modp

  /* w19 = x^3 <= x^2 * x = w25*w24 = w26*w19 */
  bn.mov    w25, w19
  bn.mov    w24, w26
  jal       x1, mul_modp

  /* w18 <= x^3 + axz^2 mod p = w19 + w18 mod p */
  bn.addm   w18, w19, w18

  /* w18 <= x^3 + axz^2 + bz^3 mod p = w19 + w27 mod p = lhs */
  bn.addm   w18, w18, w27

  /* Load projective y-coordinate of curve point from dmem
     w26 <= dmem[y] */
  la        x3, y
  li        x2, 24
  bn.lid    x2, 0(x3)

  /* w19 <= w24*w24 mod p = y^2 mod p */
  bn.mov    w25, w24
  jal       x1, mul_modp

  /* load projective z-coordinate of curve point from dmem
     w26 <= dmem[z] */
  la        x3, z
  li        x2, 24
  bn.lid    x2, 0(x3)

  /* w19 <= w26*w19 mod p = zy^2 mod p */
  bn.mov    w25, w19
  jal       x1, mul_modp

  ret
