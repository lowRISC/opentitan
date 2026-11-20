/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.globl p256_check_isoncurve

/**
 * Hardened boolean values.
 *
 * Should match the values in `hardened_asm.h`.
 */
.equ HARDENED_BOOL_TRUE, 0x739
.equ HARDENED_BOOL_FALSE, 0x1d4

/**
 * Check if a provided point in the affine form is on the P-256 curve.
 *
 * For a given curve point (x, y), check that:
 * - x and y are both fully reduced mod p (i.e. x, y < p)
 * - (x, y) is on the P-256 curve.
 *
 * This routine runs in constant time and sets `ok` to HARDENED_BOOL_TRUE if
 * the check succeeds, or HARDENED_BOOL_FALSE if the check fails.
 *
 * @param[in]  dmem[x]: Point x-coordinate.
 * @param[in]  dmem[y]: Point y-coordinate.
 * @param[out] dmem[ok]: HARDENED_BOOL_TRUE or HARDENED_BOOL_FALSE (32 bits).
 *
 * clobbered registers: x2 to x5, x19, x20, w0, w2, w18 to w29
 * clobbered flag groups: FG0
 */
p256_check_isoncurve:
  /* Init all-zero register. */
  bn.xor    w31, w31, w31

  /* Compute both sides of the Weierstrass equation.
       MOD <= p
       w18 <= (x^3 + ax + b) mod p
       w19 <= (y^2) mod p */
  jal       x1, p256_isoncurve

  /* Compare the two sides of the equation.
       FG0.Z <= (y^2) mod p == (x^3 + ax + b) mod p
       x4 <= FG0.Z (1 if on curve, 0 otherwise) */
  bn.cmp    w18, w19
  csrrs     x4, FG0, x0
  srli      x4, x4, 3
  andi      x4, x4, 1

  /* Load domain parameter p from MOD WSR.
       w29 <= MOD = p */
  bn.wsrr   w29, MOD

  /* Load point x-coordinate and compare to p.
       w2 <= dmem[x] = x
       FG0.C <= (x < p)
       x5 <= FG0.C (1 if x < p, 0 otherwise) */
  li        x2, 2
  la        x3, x
  bn.lid    x2, 0(x3)
  bn.cmp    w2, w29
  csrrs     x5, FG0, x0
  andi      x5, x5, 1
  and       x4, x4, x5

  /* Load point y-coordinate and compare to p.
       w2 <= dmem[y] = y
       FG0.C <= (y < p)
       x5 <= FG0.C (1 if y < p, 0 otherwise) */
  la        x3, y
  bn.lid    x2, 0(x3)
  bn.cmp    w2, w29
  csrrs     x5, FG0, x0
  andi      x5, x5, 1
  and       x4, x4, x5

  /* Select HARDENED_BOOL_TRUE if x4 == 1, else HARDENED_BOOL_FALSE. */
  addi      x2, x0, HARDENED_BOOL_FALSE
  addi      x3, x0, HARDENED_BOOL_TRUE
  xor       x3, x3, x2
  sub       x4, x0, x4
  and       x3, x3, x4
  xor       x3, x3, x2

  /* Write result to dmem[ok]. */
  la        x2, ok
  sw        x3, 0(x2)

  ret

.section .bss

/* Success code for basic validity checks on the public key and signature.
   Used for verify. Should be HARDENED_BOOL_TRUE or HARDENED_BOOL_FALSE. */
.balign 4
.weak ok
ok:
  .zero 4
