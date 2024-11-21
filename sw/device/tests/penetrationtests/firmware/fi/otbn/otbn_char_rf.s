/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
    OBTN.CHAR_RF FI Penetration Test
*/
.section .text.start
  /* Init GPR RF. */
  la x31, otbn_ref_values
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

  /* Init WDR RF. */
  li x1, 0
  bn.lid    x1++, 0x00(x31)
  bn.lid    x1++, 0x20(x31)
  bn.lid    x1++, 0x40(x31)
  bn.lid    x1++, 0x60(x31)
  bn.lid    x1++, 0x0(x31)
  bn.lid    x1++, 0x20(x31)
  bn.lid    x1++, 0x40(x31)
  bn.lid    x1++, 0x60(x31)
  bn.lid    x1++, 0x00(x31)
  bn.lid    x1++, 0x20(x31)
  bn.lid    x1++, 0x40(x31)
  bn.lid    x1++, 0x60(x31)
  bn.lid    x1++, 0x00(x31)
  bn.lid    x1++, 0x20(x31)
  bn.lid    x1++, 0x40(x31)
  bn.lid    x1++, 0x60(x31)
  bn.lid    x1++, 0x00(x31)
  bn.lid    x1++, 0x20(x31)
  bn.lid    x1++, 0x40(x31)
  bn.lid    x1++, 0x60(x31)
  bn.lid    x1++, 0x00(x31)
  bn.lid    x1++, 0x20(x31)
  bn.lid    x1++, 0x40(x31)
  bn.lid    x1++, 0x60(x31)
  bn.lid    x1++, 0x00(x31)
  bn.lid    x1++, 0x20(x31)
  bn.lid    x1++, 0x40(x31)
  bn.lid    x1++, 0x60(x31)
  bn.lid    x1++, 0x00(x31)
  bn.lid    x1++, 0x20(x31)
  bn.lid    x1++, 0x40(x31)
  bn.lid    x1++, 0x60(x31)

  /* 10000 NOPs (FI target). */
  loopi 10, 3
    loopi 1000, 1
      nop
    nop

  /* Read GPR RF into DMEM. */
  la x31, otbn_res_values_gpr
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

  /* Read WDR RF into DMEM. */
  la x31, otbn_res_values_wdr
  li        x1, 0
  bn.sid    x1++, 0x000(x31)
  bn.sid    x1++, 0x020(x31)
  bn.sid    x1++, 0x040(x31)
  bn.sid    x1++, 0x060(x31)
  bn.sid    x1++, 0x080(x31)
  bn.sid    x1++, 0x0a0(x31)
  bn.sid    x1++, 0x0c0(x31)
  bn.sid    x1++, 0x0e0(x31)
  bn.sid    x1++, 0x100(x31)
  bn.sid    x1++, 0x120(x31)
  bn.sid    x1++, 0x140(x31)
  bn.sid    x1++, 0x160(x31)
  bn.sid    x1++, 0x180(x31)
  bn.sid    x1++, 0x1a0(x31)
  bn.sid    x1++, 0x1c0(x31)
  bn.sid    x1++, 0x1e0(x31)
  bn.sid    x1++, 0x200(x31)
  bn.sid    x1++, 0x220(x31)
  bn.sid    x1++, 0x240(x31)
  bn.sid    x1++, 0x260(x31)
  bn.sid    x1++, 0x280(x31)
  bn.sid    x1++, 0x2a0(x31)
  bn.sid    x1++, 0x2c0(x31)
  bn.sid    x1++, 0x2e0(x31)
  bn.sid    x1++, 0x300(x31)
  bn.sid    x1++, 0x320(x31)
  bn.sid    x1++, 0x340(x31)
  bn.sid    x1++, 0x360(x31)
  bn.sid    x1++, 0x380(x31)
  bn.sid    x1++, 0x3a0(x31)
  bn.sid    x1++, 0x3c0(x31)
  bn.sid    x1++, 0x3e0(x31)

  ecall

.data
  .balign 32
  .globl otbn_ref_values
  otbn_ref_values:
    .zero 128

  .balign 32
  .globl otbn_res_values_gpr
  otbn_res_values_gpr:
    .zero 128

  .balign 32
  .globl otbn_res_values_wdr
  otbn_res_values_wdr:
    .zero 1024
