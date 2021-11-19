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

  /* set dmem to result */
  la       x2, res_r
  la       x3, dptr_r
  sw       x2, 0(x3)
  la       x2, res_l
  la       x3, dptr_s
  sw       x2, 0(x3)

  /* set dmem pointer to point to cuve point */
  la       x2, point_x
  la       x3, dptr_x
  sw       x2, 0(x3)
  la       x2, point_y
  la       x3, dptr_y
  sw       x2, 0(x3)

  /* call curve point test routine in P-384 lib */
  jal      x1, p384_isoncurve

  /* load result to WDRs for comparison with reference */
  li        x2, 0
  la        x3, res_r
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)
  la        x3, res_l
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  ecall


.data

/* buffer for right side result of Weierstrass equation */
res_r:
  .zero 64

/* buffer for left side result of Weierstrass equation */
res_l:
  .zero 64

/* point affine x-coordinate */
point_x:
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
point_y:
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

/* Expected values in wide register file:
   [w1, w0] is right side result of Weierstrass equation,
   [w3, w2] is right side result of Weierstrass equation.
   Point is on curve if [w3,w2] == [w1,w0].
 w0  = 0xfb192142f51950228765c0f69371a6a63aaff417aacdf679abcbea36b6c505b8
 w1  = 0x000000000000000000000000000000008075470ebf2179fe3a1f1fdf4b445503
 w2  = 0xfb192142f51950228765c0f69371a6a63aaff417aacdf679abcbea36b6c505b8
 w3  = 0x000000000000000000000000000000008075470ebf2179fe3a1f1fdf4b445503
*/
