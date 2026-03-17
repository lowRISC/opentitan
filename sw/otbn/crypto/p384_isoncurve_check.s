/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
 *   P-384 specific routines for ECDSA signature verification and curve point
 *   test.
 */

.globl p384_check_isoncurve

/**
 * Hardened boolean values.
 *
 * Should match the values in `hardened_asm.h`.
 */
.equ HARDENED_BOOL_TRUE, 0x739
.equ HARDENED_BOOL_FALSE, 0x1d4

 .section .text

/**
 * Check if a provided point in the affine form is on the P-384 curve.
 *
 * This routine sets `ok` to false if the check fails and immediately exits the
 * program. If the check succeeds, `ok` is unmodified.
 *
 * @param[in] dmem[x]: Point x-coordinate.
 * @param[in] dmem[y]: Point y-coordinate.
 * @param[out] dmem[ok]: success/failure of basic checks (32 bits)
 *
 */
p384_check_isoncurve:
  /* Init all-zero register. */
  bn.xor    w31, w31, w31

  /* set dmem pointer to point x-coordinate */
  la        x20, x

  /* set dmem pointer to point y-coordinate */
  la        x21, y

  /* load domain parameter p (modulus)
     [w13, w12] = p = dmem[p384_p] */
  li        x2, 12
  la        x3, p384_p
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* Load public key x-coordinate.
     [w11, w10] <= dmem[x] = x */
  li        x2, 10
  bn.lid    x2++, 0(x20)
  bn.lid    x2, 32(x20)

  /* Load public key y-coordinate.
       w2 <= dmem[y] = y */
  li        x2, 8
  bn.lid    x2++, 0(x21)
  bn.lid    x2, 32(x21)

  /* Fill gpp registers with pointers to variables */
  la        x22, rhs
  la        x23, lhs

  /* Compute both sides of the Weierstrauss equation.
       dmem[rhs] <= (x^3 + ax + b) mod p
       dmem[lhs] <= (y^2) mod p */
  jal       x1, p384_isoncurve

  /* Load both sides of the equation.
       [w5, w4] <= dmem[lhs]
       [w7, w6] <= dmem[rhs]*/
  li        x2, 4
  bn.lid    x2++, 0(x23)
  bn.lid    x2++, 32(x23)
  bn.lid    x2++, 0(x22)
  bn.lid    x2, 32(x22)

  /* Compare the two sides of the equation.
       FG0.Z <= (y^2) mod p == (x^2 + ax + b) mod p */
  bn.cmp    w4, w4
  /* Fail if FG0.Z is false. */
  jal       x1, p384_trigger_input_error_if_fg0_not_z

  bn.cmp    w5, w7
  /* Fail if FG0.Z is false. */
  jal       x1, p384_trigger_input_error_if_fg0_not_z

  /* If we got here the check passed, so set `ok` to true. */
  la       x2, ok
  addi     x3, x0, HARDENED_BOOL_TRUE
  sw       x3, 0(x2)

  ret
