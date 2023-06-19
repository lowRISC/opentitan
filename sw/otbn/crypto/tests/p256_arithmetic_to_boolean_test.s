/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone 257-bit arithmetic-to-boolean masking test
 *
 * Uses OTBN ECC P-256 lib to perform arithmetic-to-boolean conversion of
 * a given masked 257-bit value with a random mask. Afterwards it unmasks the
 * result and compares it with the initial value from DMEM.
 */

.section .text.start

p256_arithmetic_to_boolean_test:

  /* init all-zero register */
  bn.xor    w31, w31, w31

  /* Load domain parameter.
     w29 = dmem[p256_p] */
  li        x2, 29
  la        x4, p256_p
  bn.lid    x2, 0(x4)

  /* Set MOD to p */
  bn.wsrw   0x00, w29

  /* Load values into WDRs */

  /* w11 <= dmem[x_l] */
  li        x3, 11
  la        x4, x_l
  bn.lid    x3, 0(x4)

  /* w12 <= dmem[x_u] */
  li        x3, 12
  la        x4, x_u
  bn.lid    x3, 0(x4)

  /* w18 <= URND
     w19 <= URND (1 bit) */
  bn.wsrr   w18, 0x02
  bn.wsrr   w19, 0x02
  bn.rshi   w19, w31, w19 >> 255

  /* Arithmetic masking */

  /* [w12,w11] = A <= [w12,w11] - [w19,w18] mod 2^257 = x - r mod 2^257
     This may result in bits above 2^257, but these will be stripped off. */
  bn.sub    w11, w11, w18
  bn.subb   w12, w12, w19
  bn.rshi   w12, w12, w31 >> 1
  bn.rshi   w12, w31, w12 >> 255

  /* Arithmetic to boolean conversion */
  jal       x1, arithmetic_to_boolean

  /* Unmask and compare values
     after conversion */

  /* w20 <= w20 ^ w18 = x' ^ r
     w21 <= w21 ^ w19 = x' ^ r */
  bn.xor    w20, w20, w18
  bn.xor    w21, w21, w19

  /* w11 <= dmem[x_l] */
  li        x3, 11
  la        x4, x_l
  bn.lid    x3, 0(x4)

  /* w12 <= dmem[x_u] */
  li        x3, 12
  la        x4, x_u
  bn.lid    x3, 0(x4)

  /* [w1,w0] <= [w12,w11] - [w21,w20] */
  bn.sub    w0, w11, w20
  bn.subb   w1, w12, w21

  ecall


.data

.globl x_u
.balign 32
x_u:
  .word 0x00000001
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000

.globl x_l
.balign 32
x_l:
  .word 0x2ab77ca0
  .word 0x8031ceb8
  .word 0xff3e1afa
  .word 0x353ec814
  .word 0x22fe027b
  .word 0x8a29dc16
  .word 0xf7109d54
  .word 0x762c5d06
