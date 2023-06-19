/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone elliptic curve P-256 arithmetic-to-boolean masking test
 *
 * Uses OTBN ECC P-256 lib to perform arithmetic-to-boolean conversion of
 * a given masked curve value with a random mask. Afterwards it unmasks the
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

  /* w11 <= dmem[x] mod p */
  li        x3, 11
  la        x4, x
  bn.lid    x3, 0(x4)
  bn.addm   w11, w11, w31

  /* w19 <= URND mod p */
  bn.wsrr   w19, 0x02
  bn.addm   w19, w19, w31

  /* Arithmetic masking */

  /* w11 = A <= w11 - w19 = x - r */
  bn.subm    w11, w11, w19

  /* Arithmetic to boolean conversion */
  jal       x1, arithmetic_to_boolean_mod

  /* Unmask and compare values
     after conversion */

  /* w20 <= w20 ^ w19 = x' ^ r = x */
  bn.xor    w20, w20, w19

  /* w10 <= dmem[x] mod p */
  li        x3, 10
  la        x4, x
  bn.lid    x3, 0(x4)
  bn.addm   w10, w10, w31

  /* w0 <= w10 - w20 */
  bn.sub    w0, w20, w10

  ecall


.data

.globl x
.balign 32
x:
  .word 0x2ab77ca0
  .word 0x8031ceb8
  .word 0xff3e1afa
  .word 0x353ec814
  .word 0x22fe027b
  .word 0x8a29dc16
  .word 0xf7109d54
  .word 0x762c5d06
