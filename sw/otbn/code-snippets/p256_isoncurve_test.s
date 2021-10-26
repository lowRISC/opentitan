/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for P-256 curve point test
 *
 * Runs the P-256 curve point test to check whether a point (given in affine
 * space) is a valid P-256 curve point.
 * See comment at the end of the file for expected values of result.
 */

.section .text.start

p256_oncurve_test:

  /* set dmem pointers to result */
  la       x2, res_r
  la       x3, dptr_r
  sw       x2, 0(x3)
  la       x2, res_l
  la       x3, dptr_s
  sw       x2, 0(x3)

  /* set dmem pointer to point to curve point */
  la       x2, point_x
  la       x3, dptr_x
  sw       x2, 0(x3)
  la       x2, point_y
  la       x3, dptr_y
  sw       x2, 0(x3)

  /* call curve point test routine in P-256 lib */
  jal      x1, p256_isoncurve

  /* load result to WDRs for comparison with reference */
  li        x2, 0
  la        x3, res_r
  bn.lid    x2++, 0(x3)
  la        x3, res_l
  bn.lid    x2, 0(x3)

  ecall


.data

/* buffer for right side result of Weierstrass equation */
res_r:
  .zero 32

/* buffer for left side result of Weierstrass equation */
res_l:
  .zero 32

/* point affine x-coordinate */
point_x:
  .word 0xbfa8c334
  .word 0x9773b7b3
  .word 0xf36b0689
  .word 0x6ec0c0b2
  .word 0xdb6c8bf3
  .word 0x1628ce58
  .word 0xfacdc546
  .word 0xb5511a6a

/* point affine y-coordinate */
point_y:
  .word 0x9e008c2e
  .word 0xa8707058
  .word 0xab9c6924
  .word 0x7f7a11d0
  .word 0xb53a17fa
  .word 0x43dd09ea
  .word 0x1f31c143
  .word 0x42a1c697

/* Expected values wide register file (w0=R, w1=S):
w0 = 0xb103b614b389c6b8e1a08330a6ce0b9c4b3726ec0bf61f6bdd66af03a4af5660
w1 = 0xb103b614b389c6b8e1a08330a6ce0b9c4b3726ec0bf61f6bdd66af03a4af5660
*/
