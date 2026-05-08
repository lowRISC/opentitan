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
 * This routine sets `ok` to false if the check fails and immediately exits the
 * program. If the check succeeds, `ok` is unmodified.
 *
 * @param[in] dmem[x]: Point x-coordinate.
 * @param[in] dmem[y]: Point y-coordinate.
 * @param[out] dmem[ok]: success/failure of basic checks (32 bits)
 *
 */
p256_check_isoncurve:
  /* Init all-zero register. */
  bn.xor   w31, w31, w31

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
  bne       x2, x0, _p256_point_on_curve
  jal       x0, p256_not_on_curve

  /* Extra unimps in case an attacker tries to skip the jump. */
  unimp
  unimp
  unimp

  _p256_point_on_curve:

  /* If we got here the check passed, so set `ok` to true. */
  la       x2, ok
  addi     x3, x0, HARDENED_BOOL_TRUE
  sw       x3, 0(x2)

  ret

/**
 * Failure case for the is on curve check.
 *
 * This routine sets `ok` to false if the check fails.
 *
 * @param[out] dmem[ok] Set to HARDENED_BOOL_FALSE.
 */
p256_not_on_curve:
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
