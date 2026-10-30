/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/*
  Read MAI_STATUS in the last busy cycle of each MAI operation, and in the
  cycle after it.

  In the RTL, BUSY reads 0 from the 16th instruction after the START write of
  a secAdd and from the 24th after that of a secAddMod or an A2B. A B2A takes
  one cycle more for its output register. The first read of each pair sees
  BUSY and INPUT_READY (0x3), the second only INPUT_READY (0x2). MOD is close
  to 2^32 so that B2A practically never rejects a mask.
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
  .rept 14
  addi      x0, x0, 0
  .endr
  csrrs     x2, MAI_STATUS, x0
  csrrs     x3, MAI_STATUS, x0

  /* secAddMod */
  li        x10, 0x19
  csrrw     x0, MAI_CTRL, x10
  .rept 22
  addi      x0, x0, 0
  .endr
  csrrs     x5, MAI_STATUS, x0
  csrrs     x6, MAI_STATUS, x0

  /* A2B */
  li        x10, 0x17
  csrrw     x0, MAI_CTRL, x10
  .rept 22
  addi      x0, x0, 0
  .endr
  csrrs     x8, MAI_STATUS, x0
  csrrs     x9, MAI_STATUS, x0

  /* B2A */
  li        x10, 0x21
  csrrw     x0, MAI_CTRL, x10
  .rept 23
  addi      x0, x0, 0
  .endr
  csrrs     x11, MAI_STATUS, x0
  csrrs     x12, MAI_STATUS, x0

  ecall

.data
.balign 32
modv:
  .word 0xfffffffb
  .zero 28
