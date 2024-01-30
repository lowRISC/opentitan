/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.globl p256_isoncurve
.globl p256_check_public_key
.globl p256_invalid_input

/**
 * Hardened boolean values.
 *
 * Should match the values in `hardened_asm.h`.
 */
.equ HARDENED_BOOL_TRUE, 0x739
.equ HARDENED_BOOL_FALSE, 0x1d4

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

/**
 * Check if a provided public key is valid.
 *
 * For a given public key (x, y), check that:
 * - x and y are both fully reduced mod p
 * - (x, y) is on the P-256 curve.
 *
 * Note that, because the point is in affine form, it is not possible that (x,
 * y) is the point at infinity. In some other forms such as projective
 * coordinates, we would need to check for this also.
 *
 * This routine sets `ok` to false if the check fails and immediately exits the
 * program. If the check succeeds, `ok` is unmodified.
 *
 * @param[in] dmem[x]: Public key x-coordinate.
 * @param[in] dmem[y]: Public key y-coordinate.
 * @param[out] dmem[ok]: success/failure of basic checks (32 bits)
 *
 * clobbered registers: x2, x3, x19, x20, w0, w2, w19 to w29
 * clobbered flag groups: FG0
 */
p256_check_public_key:
  /* Init all-zero register. */
  bn.xor   w31, w31, w31

  /* Load domain parameter p.
       w29 <= dmem[p256_p] = p */
  li        x2, 29
  la        x3, p256_p
  bn.lid    x2, 0(x3)

  /* Load public key x-coordinate.
       w2 <= dmem[x] = x */
  li        x2, 2
  la        x3, x
  bn.lid    x2, 0(x3)

  /* Compare x to p.
       FG0.C <= (x < p) */
  bn.cmp    w2, w29

  /* Fail if FG0.C is false. */
  csrrs     x2, FG0, x0
  andi      x2, x2, 1
  bne       x2, x0, _x_valid
  jal       x0, p256_invalid_input
  unimp

  _x_valid:

  /* Load public key y-coordinate.
       w2 <= dmem[y] = y */
  li        x2, 2
  la        x3, y
  bn.lid    x2, 0(x3)

  /* Compare y to p.
       FG0.C <= (y < p) */
  bn.cmp    w2, w29

  /* Fail if FG0.C is false. */
  csrrs     x2, FG0, x0
  andi      x2, x2, 1
  bne       x2, x0, _y_valid
  jal       x0, p256_invalid_input
  unimp

  _y_valid:

  /* Compute both sides of the Weierstrauss equation.
       w18 <= (x^3 + ax + b) mod p
       w19 <= (y^2) mod p */
  jal      x1, p256_isoncurve

  /* Compare the two sides of the equation.
       FG0.Z <= (y^2) mod p == (x^2 + ax + b) mod p */
  bn.cmp    w18, w19

  /* Fail if FG0.Z is false; otherwise return. */
  csrrs     x2, FG0, x0
  andi      x2, x2, 8
  bne       x2, x0, _xy_on_curve
  jal       x0, p256_invalid_input

  /* Extra unimps in case an attacker tries to skip the jump. */
  unimp
  unimp
  unimp

  _xy_on_curve:
  ret

/**
 * Failure cases for basic validity checks jump here.
 *
 * This routine sets `ok` to false if the check fails.
 *
 * @param[out] dmem[ok] Set to HARDENED_BOOL_FALSE.
 */
p256_invalid_input:
  /* Set the `ok` code to false. */
  la       x2, ok
  addi     x3, x0, HARDENED_BOOL_FALSE
  sw       x3, 0(x2)

  /* End the program. */
  ecall

.section .bss

/* Success code for basic validity checks on the public key and signature.
   Used for verify. Should be HARDENED_BOOL_TRUE or HARDENED_BOOL_FALSE. */
.balign 4
.weak ok
ok:
  .zero 4
