/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/*
  Read MAI_STATUS in the last cycle before INPUT_READY rises after the START
  write of each MAI operation, and in the cycle after it.

  In the RTL, the accelerator takes one input element per cycle and
  INPUT_READY reads 1 again from the 9th instruction after the START write.
  The first read of each pair sees only BUSY (0x1), the second BUSY and
  INPUT_READY (0x3). MOD is close to 2^32 so that B2A practically never
  rejects a mask.
*/

  bn.xor    w0, w0, w0
  la        x2, modv
  li        x3, 1
  bn.lid    x3, 0(x2)
  bn.wsrw   MOD, w1
  bn.wsrw   MAI_IN0_S0, w0
  bn.wsrw   MAI_IN0_S1, w0
  bn.wsrw   MAI_IN1_S0, w0
  bn.wsrw   MAI_IN1_S1, w0

  /* secAdd */
  li        x10, 0x2f
  csrrw     x0, MAI_CTRL, x10
  .rept 7
  addi      x0, x0, 0
  .endr
  csrrs     x2, MAI_STATUS, x0
  csrrs     x3, MAI_STATUS, x0
  jal       x1, wait_idle

  /* secAddMod */
  li        x10, 0x19
  csrrw     x0, MAI_CTRL, x10
  .rept 7
  addi      x0, x0, 0
  .endr
  csrrs     x5, MAI_STATUS, x0
  csrrs     x6, MAI_STATUS, x0
  jal       x1, wait_idle

  /* A2B */
  li        x10, 0x17
  csrrw     x0, MAI_CTRL, x10
  .rept 7
  addi      x0, x0, 0
  .endr
  csrrs     x8, MAI_STATUS, x0
  csrrs     x9, MAI_STATUS, x0
  jal       x1, wait_idle

  /* B2A */
  li        x10, 0x21
  csrrw     x0, MAI_CTRL, x10
  .rept 7
  addi      x0, x0, 0
  .endr
  csrrs     x11, MAI_STATUS, x0
  csrrs     x12, MAI_STATUS, x0

  ecall

/* Wait until the MAI is no longer busy. */
wait_idle:
  csrrs     x4, MAI_STATUS, x0
  andi      x4, x4, 1
  bne       x4, x0, wait_idle
  ret

.data
.balign 32
modv:
  .word 0xfffffffb
  .zero 28
