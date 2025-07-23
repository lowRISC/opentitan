/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone elliptic curve P-384 ECDH shared key generation test
 *
 * Uses OTBN ECC P-384 lib to perform a scalar multiplication with a valid
 * example curve point and an example scalar. Both scalar and coordinates of
 * the curve point are contained in the .data section below.
 * The x coordinate of the resulting curve point is masked arithmetically
 * with a random value. As the x coorodinate represents the actual
 * shared key, the x coordinate and its mask are then converted from an
 * arithmetic to a boolean masking scheme.
 *
 * The result of boolean unmasking is then compared with the expected shared
 * key value.
 */

.section .text.start

p384_ecdh_shared_key_test:
  /* init all-zero register */
  bn.xor    w31, w31, w31

  /* fill gpp registers with pointers to relevant variables */
  /*la        x17, k0
  la        x19, k1
  la        x20, x
  la        x21, y

  /* call scalar point multiplication routine in P-384 lib */
  jal       x1, p384_scalar_mult

  /* load result to WDRs for unmasking and comparison with reference
     [w12,w11] <= dmem[p1_x] = x_m
     [w19,w18] <= dmem[p1_y] = m */
  li        x2, 11
  la        x3, x
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)
  li        x2, 18
  la        x3, y
  bn.lid    x2++, 0(x3)
  bn.lid    x2, 32(x3)

  /* Load domain parameter.
     [w14,w13] = dmem[p384_p] */
  li        x2, 13
  la        x4, p384_p
  bn.lid    x2++, 0(x4)
  bn.lid    x2++, 32(x4)

  /* Arithmetic to boolean conversion */
  jal       x1, p384_arithmetic_to_boolean_mod

  /* Boolean unmasking of result value
     [w21,w20] <= [w21,w20] ^ [w19,w18] */
  bn.xor    w0, w20, w18
  bn.xor    w1, w21, w19

  ecall


.data

.balign 32

/* point 1 x-cooridante x */
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

/* point 1 y-cooridante y*/
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
