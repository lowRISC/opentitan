/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone 384-bit boolean-to-arithmetic masking test
 *
 * Uses OTBN ECC P-384 lib to perform arithmetic-to-boolean conversion of
 * a given masked 384-bit value with a random mask. Afterwards it unmasks the
 * result and compares it with the initial value from DMEM.
 */

.section .text.start

p384_boolean_to_arithmetic_test:

  /* init all-zero register */
  bn.xor    w31, w31, w31

  /* Load values into WDRs */

  /* w20 <= dmem[x_l] */
  li        x3, 20
  la        x4, x_l
  bn.lid    x3, 0(x4)

  /* w21 <= dmem[x_u] */
  li        x3, 21
  la        x4, x_u
  bn.lid    x3, 0(x4)

  /* w10 <= URND
     w11 <= URND (128 bits) */
  bn.wsrr   w10, URND
  bn.wsrr   w11, URND
  bn.rshi   w11, w31, w11 >> 128

  /* Boolean masking */

  /* [w21,w20] = x' <= [w11,w10] ^ [w21,w20] = x ^ r */
  bn.xor    w20, w10, w20
  bn.xor    w21, w11, w21

  /* Arithmetic to boolean conversion */
  jal       x1, p384_boolean_to_arithmetic

  /* Unmask and compare values
     after conversion */

  /* [w21,w20] <= [w21,w20] + [w11,w10] = A + r */
  bn.add    w20, w20, w10
  bn.addc   w21, w21, w11

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
  .word 0xab0f7698
  .word 0xc85b787e
  .word 0x9d9c9644
  .word 0x9f740ded
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
