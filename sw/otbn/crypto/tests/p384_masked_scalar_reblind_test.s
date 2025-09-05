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

p384_masked_scalar_reblind_test:

  /* Init all-zero register. */
  bn.xor  w31, w31, w31

  /* call masked scalar reblind routine */
  jal      x1, p384_masked_scalar_reblind

  ecall
