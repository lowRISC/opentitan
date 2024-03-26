/* Copyright lowRISC contributors. */
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
  la        x17, k0
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
  .word 0x1a11808b
  .word 0x02e3d5a9
  .word 0x440d8db6
  .word 0x5ef02be3
  .word 0x2a35de10
  .word 0xdbdb132e
  .word 0xf84e7899
  .word 0x7dff4c2b
  .word 0x24705317
  .word 0x30eda4ab
  .word 0xb44ba799
  .word 0x3af8f1c5
  .zero 16

/* point 1 y-cooridante y*/
.globl y
y:
  .word 0xa9f8b96e
  .word 0x82f268be
  .word 0x8e51c662
  .word 0x92b9c4bb
  .word 0x757d4493
  .word 0x26b4d3c6
  .word 0xf491007e
  .word 0x92a5c72a
  .word 0x8d8d8641
  .word 0x87498a20
  .word 0x0fe7dbde
  .word 0x841e4949
  .zero 16

/* 1st scalar share k0 (448-bit) */
.globl k0
k0:
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

/* 2nd scalar share k1 (448-bit) */
.globl k1
k1:
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

/* scalar k = (k0 + k1) mod n (384-bit)*/
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
