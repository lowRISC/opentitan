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

p384_scalar_mult_test:

  /* Init all-zero register. */
  bn.xor  w31, w31, w31

  /* call scalar point multiplication routine in P-384 lib */
  jal      x1, p384_scalar_mult

  /* load result to WDRs for comparison with reference */
  li        x2, 0
  la        x3, x
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)
  la        x3, y
  bn.lid    x2++, 0(x3)
  bn.lid    x2, 32(x3)

  /* load domain parameter p (modulus)
     [w13, w12] = p = dmem[p384_p] */
  li        x2, 12
  la        x3, p384_p
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* unmask x coordinate x = x_m + m mod p = x-coord. + y-coord. mod p */
  bn.add    w0, w0, w2
  bn.addc   w1, w1, w3

  bn.mov    w18, w0
  bn.mov    w19, w1
  bn.mov    w20, w31
  jal       x1, p384_reduce_p
  bn.mov    w0, w16
  bn.mov    w1, w17

  ecall


.section .data

.balign 32

/* point 1 x-cooridante p1_x */
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

/* point 1 y-cooridante p1_y*/
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

/* 1st scalar share d0 (448-bit) */
.globl d0
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

/* scalar d = (d0 + d1) mod n (384-bit)*/
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
