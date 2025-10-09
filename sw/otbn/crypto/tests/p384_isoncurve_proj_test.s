/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for P-384 curve point test
 *
 * Runs the P-384 curve point test to check whether a point (given in projective
 * space) is a valid P-384 curve point.
 * See comment at the end of the file for expected values of result.
 */

.section .text.start

p384_isoncurve_proj_test:
  /* load domain parameter p (modulus)
     [w13, w12] = p = dmem[p384_p] */
  li        x2, 12
  la        x3, p384_p
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* Fill gpr registers with pointers to variables */
  la        x20, x
  la        x21, y
  la        x30, z

  /* call curve point test routine in P-384 lib */
  jal       x1, p384_isoncurve_proj_check

  /* load result to WDRs for comparison with reference */
  li        x2, 0
  bn.lid    x2++, 0(x22)
  bn.lid    x2++, 32(x22)
  bn.lid    x2++, 0(x23)
  bn.lid    x2++, 32(x23)

  ecall


.data

/* point projective z-coordinate */
.globl z
z:
  .zero 64
