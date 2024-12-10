/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
    OBTN.CHAR_BN_WSRR FI Penetration Test
*/
.section .text.start
  /* Load random values into w0...w31 (FI target). */
  bn.wsrr w0,  URND
  bn.wsrr w1,  URND
  bn.wsrr w2,  URND
  bn.wsrr w3,  URND
  bn.wsrr w4,  URND
  bn.wsrr w5,  URND
  bn.wsrr w6,  URND
  bn.wsrr w7,  URND
  bn.wsrr w8,  URND
  bn.wsrr w9,  URND
  bn.wsrr w10, URND
  bn.wsrr w11, URND
  bn.wsrr w12, URND
  bn.wsrr w13, URND
  bn.wsrr w14, URND
  bn.wsrr w15, URND
  bn.wsrr w16, URND
  bn.wsrr w17, URND
  bn.wsrr w18, URND
  bn.wsrr w19, URND
  bn.wsrr w20, URND
  bn.wsrr w21, URND
  bn.wsrr w22, URND
  bn.wsrr w23, URND
  bn.wsrr w24, URND
  bn.wsrr w25, URND
  bn.wsrr w26, URND
  bn.wsrr w27, URND
  bn.wsrr w28, URND
  bn.wsrr w29, URND
  bn.wsrr w30, URND
  bn.wsrr w31, URND

  /* 1000 NOPs*/
  loopi 10, 3
    loopi 100, 1
      nop
    nop

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
  .globl otbn_res_values_wdr
  otbn_res_values_wdr:
    .zero 1024
