/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
 *   Standalone test for P-384 scalar multiplication with base point.
 *
 *   Performs multiplication of the base point of P-384 by a scalar. This
 *   resembles computing the public key for a given private key. The scalar
 *   (private key) is contained in the .data section below.
 *
 *   See comment at the end of the file for expected values of coordinates
 *   of resulting point.
 */

.section .text.start

p384_base_mult_test:

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

  /* call base point multiplication routine in P-384 lib */
  jal      x1, p384_base_mult

  /* load result to WDRs for comparison with reference */
  li        x2, 0
  la        x3, p1_x
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)
  la        x3, p1_y
  bn.lid    x2++, 0(x3)
  bn.lid    x2, 32(x3)

  ecall


.section .data

/* scalar d */
scalar:
  .word 0xe8791ba3
  .word 0xf549e1f7
  .word 0x893be358
  .word 0x100794fe
  .word 0xbc9db95d
  .word 0xfd7ed624
  .word 0xc60ebab6
  .word 0x97ba9586
  .word 0xa026b431
  .word 0x37112316
  .word 0x8b26eef1
  .word 0xc1a0cf66
  .zero 16

   /* blinding parameter rnd */
 blinding_param:
  .word 0xa82c85b0
  .word 0x163ce1c8
  .word 0x32518fd7
  .word 0xf8a428cd
  .word 0xf5b9d867
  .word 0x00906f5f
  .word 0x7387b4f2
  .word 0xa2d3da7a
  .word 0xebe0a647
  .word 0xfb2ef7ca
  .word 0x74249432
  .word 0x230e5ff6
  .zero 16

/* result buffer x-coordinate */
p1_x:
  .zero 64

/* result buffer y-coordinate */
p1_y:
  .zero 64
