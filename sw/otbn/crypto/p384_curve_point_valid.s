/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Curve point validation for curve P-384.
 *
 * Checks if a given curve point (e.g. public key for ECDH shared key
 * generation) is a valid curve point on the P-384 curve.
 *
 * The check is successful when the binary execution completes without
 * error. In case of an unvalid point, a software error is raised and execution
 * is halted.
 */

.section .text.start
start:
  /* Init all-zero register. */
  bn.xor    w31, w31, w31

  jal       x1, validate_point

  /* Unsupported mode; fail. */
  unimp
  unimp
  unimp

validate_point:
  /* Call curve point validation function */
  jal       x1, p384_curve_point_valid

  ecall

.data

/* Public key x-coordinate. */
.globl x
.balign 32
x:
  .zero 64

/* Public key y-coordinate. */
.globl y
.balign 32
y:
  .zero 64
