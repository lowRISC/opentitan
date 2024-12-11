/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
    OBTN.CHAR.LW FI Penetration Test
*/
.section .text.start
  /* Load values from DMEM into a register (FI target). */
  la x31, mem_in
  lw x2, 0(x31)
  lw x3, 4(x31)
  lw x4, 8(x31)
  lw x5, 12(x31)
  lw x6, 16(x31)
  lw x7, 20(x31)
  lw x8, 24(x31)
  lw x9, 28(x31)
  lw x10, 32(x31)
  lw x11, 36(x31)
  lw x12, 40(x31)
  lw x13, 44(x31)
  lw x14, 48(x31)
  lw x15, 52(x31)
  lw x16, 56(x31)
  lw x17, 60(x31)
  lw x18, 64(x31)
  lw x19, 68(x31)
  lw x20, 72(x31)
  lw x21, 76(x31)
  lw x22, 80(x31)
  lw x23, 84(x31)
  lw x24, 88(x31)
  lw x25, 92(x31)
  lw x26, 96(x31)
  lw x27, 100(x31)
  lw x28, 104(x31)
  lw x29, 108(x31)
  lw x30, 112(x31)

  /* 1000 NOPs to not accidentally hit the instructions below. */
  loopi 10, 3
    loopi 100, 1
      nop
    nop

  /* Store values from registers into DMEM. */
  la x31, mem_out
  sw x2, 0(x31)
  sw x3, 4(x31)
  sw x4, 8(x31)
  sw x5, 12(x31)
  sw x6, 16(x31)
  sw x7, 20(x31)
  sw x8, 24(x31)
  sw x9, 28(x31)
  sw x10, 32(x31)
  sw x11, 36(x31)
  sw x12, 40(x31)
  sw x13, 44(x31)
  sw x14, 48(x31)
  sw x15, 52(x31)
  sw x16, 56(x31)
  sw x17, 60(x31)
  sw x18, 64(x31)
  sw x19, 68(x31)
  sw x20, 72(x31)
  sw x21, 76(x31)
  sw x22, 80(x31)
  sw x23, 84(x31)
  sw x24, 88(x31)
  sw x25, 92(x31)
  sw x26, 96(x31)
  sw x27, 100(x31)
  sw x28, 104(x31)
  sw x29, 108(x31)
  sw x30, 112(x31)

  ecall

.data
  .balign 32
  .globl mem_in
  mem_in:
    .zero 128

  .balign 32
  .globl mem_out
  mem_out:
    .zero 128
