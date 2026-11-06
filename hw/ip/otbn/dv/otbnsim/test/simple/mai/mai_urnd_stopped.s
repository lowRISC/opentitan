/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/*
  Stop URND and read its state before and after each MAI operation.

  A busy MAI forces the stopped URND PRNG to advance. In the RTL, it advances
  in the cycle of the START write and in every busy cycle: 16 times for a
  secAdd, 24 for a secAddMod or an A2B and 25 for a B2A. MOD is close to 2^32
  so that B2A practically never rejects a mask.
*/

  bn.xor    w0, w0, w0
  la        x2, modv
  li        x3, 0
  bn.lid    x3, 0(x2)
  bn.wsrw   MOD, w0
  bn.xor    w0, w0, w0
  bn.wsrw   MAI_IN0_S0, w0
  bn.wsrw   MAI_IN0_S1, w0
  bn.wsrw   MAI_IN1_S0, w0
  bn.wsrw   MAI_IN1_S1, w0

  /* Stop URND. */
  li        x2, 1
  csrrw     x0, URND_CTRL, x2
  bn.wsrr   w1, URND_STATE

  /* secAdd */
  li        x10, 0x2f
  csrrw     x0, MAI_CTRL, x10
  .rept 30
  addi      x0, x0, 0
  .endr
  bn.wsrr   w2, URND_STATE

  /* secAddMod */
  li        x10, 0x19
  csrrw     x0, MAI_CTRL, x10
  .rept 30
  addi      x0, x0, 0
  .endr
  bn.wsrr   w3, URND_STATE

  /* A2B */
  li        x10, 0x17
  csrrw     x0, MAI_CTRL, x10
  .rept 30
  addi      x0, x0, 0
  .endr
  bn.wsrr   w4, URND_STATE

  /* B2A */
  li        x10, 0x21
  csrrw     x0, MAI_CTRL, x10
  .rept 30
  addi      x0, x0, 0
  .endr
  bn.wsrr   w5, URND_STATE

  ecall

.data
.balign 32
modv:
  .word 0xfffffffb
  .zero 28
