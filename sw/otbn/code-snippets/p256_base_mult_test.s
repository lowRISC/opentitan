/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
 *   Standalone test for P-256 scalar multiplication with base point.
 *
 *   Performs multiplication of the base point of P-256 by a scalar. This
 *   resembles computing the public key for a given private key. The scalar
 *   (private key) is contained in the .data section below.
 *
 *   See comment at the end of the file for expected values of coordinates
 *   of resulting point.
 */

.section .text.start

p256_base_mult_test:

  /* set dmem pointer to point to scalar (private key) d */
  la       x2, scalar
  la       x3, dptr_d
  sw       x2, 0(x3)

  /* set dmem pointer to point to blinding parameter */
  la       x2, blinding_param
  la       x3, dptr_rnd
  sw       x2, 0(x3)

  /* set dmem pointer to point to x-coordinate */
  la       x2, p1_x
  la       x3, dptr_x
  sw       x2, 0(x3)

  /* set dmem pointer to point to y-coordinate */
  la       x2, p1_y
  la       x3, dptr_y
  sw       x2, 0(x3)

  /* call base point multiplication routine in P-256 lib */
  jal      x1, p256_base_mult

  /* load result to WDRs for comparison with reference */
  li        x2, 0
  la        x3, p1_x
  bn.lid    x2++, 0(x3)
  la        x3, p1_y
  bn.lid    x2, 0(x3)

  ecall


.data

/* scalar d */
scalar:
  .word 0xc7df1a56
  .word 0xfbd94efe
  .word 0xaa847f52
  .word 0x2d869bf4
  .word 0x543b963b
  .word 0xe5f2cbee
  .word 0x9144233d
  .word 0xc0fbe256

   /* blinding parameter rnd */
 blinding_param:
  .word 0x7ab203c3
  .word 0xd6ee4951
  .word 0xd5b89b43
  .word 0x409d2b56
  .word 0x8e9d2186
  .word 0x1de0f8ec
  .word 0x0fa0bf9a
  .word 0xa21c2147

/* result buffer x-coordinate */
p1_x:
  .zero 32

/* result buffer y-coordinate */
p1_y:
  .zero 32

/* Expected values in wide register file (x- and y-coordinates of result):
   w0 is affine x-coordinate of resulting point,
   w1 is affine y-coordinate of resulting point.
 w0  = 0xb5511a6afacdc5461628ce58db6c8bf36ec0c0b2f36b06899773b7b3bfa8c334
 w1  = 0x42a1c6971f31c14343dd09eab53a17fa7f7a11d0ab9c6924a87070589e008c2e
*/
