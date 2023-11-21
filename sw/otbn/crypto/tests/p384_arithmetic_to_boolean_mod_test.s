/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone elliptic curve P-384 arithmetic-to-boolean masking test
 *
 * Uses OTBN ECC P-384 lib to perform arithmetic-to-boolean conversion of
 * a given masked curve value with a random mask. Afterwards it unmasks the
 * result and compares it with the initial value from DMEM.
 */

.section .text.start

p256_arithmetic_to_boolean_test:

  /* init all-zero register */
  bn.xor    w31, w31, w31

  /* Load domain parameter.
     [w13,w12] = dmem[p384_p] */
  li        x2, 12
  la        x4, p384_p
  bn.lid    x2++, 0(x4)
  bn.lid    x2++, 32(x4)

  /* Load values into WDRs */

  /* [w20,w19,w18] <= dmem[x] */
  li        x3, 18
  la        x4, x
  bn.lid    x3++, 0(x4)
  bn.lid    x3++, 32(x4)
  bn.mov    w20, w31

  /* Reduce x mod p
     [w5,w4] <= [w20,w19,w18] mod [w13,w12] = x mod p
     dmem[x] <= [w31,w5,w4] = x mod p */
  jal       x1, p384_reduce_p
  bn.mov    w4, w16
  bn.mov    w5, w17
  li        x3, 4
  la        x4, x
  bn.sid    x3++, 0(x4)
  bn.sid    x3++, 32(x4)
  li        x3, 31
  bn.sid    x3, 64(x4)

  /* [w20,w19,w18] <= URND = r */
  bn.wsrr   w18, URND
  bn.wsrr   w19, URND
  bn.wsrr   w20, URND

  /* Reduce r mod p
     [w7,w6] <= [w20,w19,w18] mod [w13,w12] = r mod p */
  jal       x1, p384_reduce_p
  bn.mov    w6, w16
  bn.mov    w7, w17

  /* Arithmetic masking.
     [w12,w11] = A <= [w5,w4] - [w7,w6] mod [w13,w12] = x - r mod p */

  /* [w19,w18] = A1 <= [w5,w4] - [w7,w6] = x - r */
  bn.sub    w18, w4, w6
  bn.subb   w19, w5, w7

  /* [w17,w16] = A2 <= [w19,w18] + [w13,w12] = A1 + p = x - r + p */
  bn.add    w16, w18, w12
  bn.addc   w17, w19, w13

  /* If x >= r: [w12,w11] <= A1, else: [w12,w11] <= A2 */
  bn.sub    w0, w4, w6
  bn.subb   w1, w5, w7
  bn.sel    w11, w16, w18, FG0.C
  bn.sel    w12, w17, w19, FG0.C

  /* Load domain parameter.
     [w14,w13] = dmem[p384_p] */
  li        x2, 13
  la        x4, p384_p
  bn.lid    x2++, 0(x4)
  bn.lid    x2++, 32(x4)

  /* Move mask r to input registers.
     [w19,18] <= [w7,w6] = r */
  bn.mov    w18, w6
  bn.mov    w19, w7

  /* Arithmetic to boolean conversion */
  jal       x1, p384_arithmetic_to_boolean_mod

  /* Unmask and compare values
     after conversion */

  /* w20 <= w20 ^ w18 = x' ^ r
     w21 <= w21 ^ w19 = x' ^ r */
  bn.xor    w20, w20, w18
  bn.xor    w21, w21, w19

  /* [w5,w4] <= dmem[x] = x mod p */
  li        x3, 4
  la        x4, x
  bn.lid    x3++, 0(x4)
  bn.lid    x3++, 32(x4)

  /* [w1,w0] <= [w12,w11] - [w21,w20] */
  bn.sub    w0, w4, w20
  bn.subb   w1, w5, w21

  ecall


.data

.globl x
.balign 32
x:
  .word 0xab0f7698
  .word 0xc85b787e
  .word 0x9d9c9644
  .word 0x9f740ded
  .word 0xa1b6fca8
  .word 0x8cd4a7b3
  .word 0x9f7fdc63
  .word 0x74013528
  .word 0x2ab77ca0
  .word 0x8031ceb8
  .word 0xff3e1afa
  .word 0x353ec814
  .word 0x22fe027b
  .word 0x8a29dc16
  .word 0xf7109d54
  .word 0x762c5d06
