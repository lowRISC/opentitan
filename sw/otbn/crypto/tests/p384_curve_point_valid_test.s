/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for P-384 curve point test
 *
 * Runs the P-384 curve point test to check whether a point (given in affine
 * space) is a valid P-384 curve point.
 */

.section .text.start

p384_curve_point_valid_test:
  /* Init all-zero register. */
  bn.xor    w31, w31, w31

  jal       x1, p384_check_isoncurve

  /* Reaching here means the check succeeded (invalid points exit early). */
  li        x2, 1

  ecall
