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
  /* call base point multiplication routine in P-384 lib */
  jal       x1, p384_base_mult

  /* load result to WDRs for comparison with reference */
  li        x2, 0
  la        x3, x
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)
  la        x3, y
  bn.lid    x2++, 0(x3)
  bn.lid    x2, 32(x3)

  ecall


.section .data

/* 1st scalar share d0 (448-bit) */
.globl d0
.balign 32
d0:
  .word 0x5c832a51
  .word 0x3eb17c27
  .word 0x9a0c1b76
  .word 0x6e001281
  .word 0x4de8344e
  .word 0x5b7d3b0f
  .word 0x96d2f9e0
  .word 0x1e9d19e7
  .word 0x16f5c1ee
  .word 0x800a4c94
  .word 0xe14cd8df
  .word 0xadb9ce1b
  .word 0x8677a5f2
  .word 0x32f9e2b0
  .zero 8

/* 2nd scalar share d1 (448-bit) */
.globl d1
.balign 32
d1:
  .word 0x33eae098
  .word 0xd31b18d5
  .word 0x507568cd
  .word 0xab8fb14d
  .word 0x9ef51898
  .word 0x44676e61
  .word 0x9cb814d9
  .word 0x4ad22b6e
  .word 0x8930f243
  .word 0xb706d682
  .word 0xa9da1611
  .word 0x13e7014a
  .word 0x9ec9b430
  .word 0x9e5dc598
  .zero 8

/* scalar d = (d0 + d1) mod n (384-bit) */
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

/* result buffer x-coordinate */
.globl x
.balign 32
x:
  .zero 64

/* result buffer y-coordinate */
.globl y
.balign 32
y:
  .zero 64
