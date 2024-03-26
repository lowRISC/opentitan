/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for P-384 curve point test
 *
 * Runs the P-384 curve point test to check whether a point (given in affine
 * space) is a valid P-384 curve point.
 * See comment at the end of the file for expected values of result.
 */

.section .text.start

p384_oncurve_test:
  /* load domain parameter p (modulus)
     [w13, w12] = p = dmem[p384_p] */
  li        x2, 12
  la        x3, p384_p
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* Fill gpp registers with pointers to variables */
  la        x20, x
  la        x21, y
  la        x22, rhs
  la        x23, lhs

  /* call curve point test routine in P-384 lib */
  jal       x1, p384_isoncurve

  /* load result to WDRs for comparison with reference */
  li        x2, 0
  bn.lid    x2++, 0(x22)
  bn.lid    x2++, 32(x22)
  bn.lid    x2++, 0(x23)
  bn.lid    x2++, 32(x23)

  ecall


.data

/* buffer for right side result of Weierstrass equation */
.globl rhs
rhs:
  .zero 64

/* buffer for left side result of Weierstrass equation */
.globl lhs
lhs:
  .zero 64

/* point affine x-coordinate */
.globl x
x:
  .word 0x4877f3d1
  .word 0x7b829460
  .word 0xb1cac609
  .word 0x5869de54
  .word 0xee0e2beb
  .word 0x6c30f2d8
  .word 0x47e80661
  .word 0x394d8b70
  .word 0xcf60d89e
  .word 0x1a9ea916
  .word 0xb439d701
  .word 0xca230836
  .zero 16

/* point affine y-coordinate */
.globl y
y:
  .word 0xc181f90f
  .word 0xc31ef079
  .word 0xbf3aff6e
  .word 0xc7e55880
  .word 0xec18818c
  .word 0xcea028a9
  .word 0x928c3e92
  .word 0x82b63bf3
  .word 0xd65e905d
  .word 0x68eef2d1
  .word 0x03afe2c2
  .word 0xaaafcad2
  .zero 16
