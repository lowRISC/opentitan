/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
    OBTN.KEY_SIDELOAD FI Penetration Test
*/
.section .text.start

    /* Load all key shares into w20...w23. */
    bn.wsrr  w20, KEY_S0_L
    bn.wsrr  w21, KEY_S1_L
    bn.wsrr  w22, KEY_S0_H
    bn.wsrr  w23, KEY_S1_H

    /* w8 <= KEY_S0_L ^ KEY_S1_L */
    bn.xor  w8, w20, w21

    /* w9 <= KEY_S0_H ^ KEY_S1_H */
    bn.xor  w9, w22, w23

    /* Write shares and keys into accessible DMEM. */
    li      x2, 20
    la      x3, k_s0_l
    bn.sid  x2, 0(x3)

    li      x2, 21
    la      x3, k_s0_h
    bn.sid  x2, 0(x3)

    li      x2, 22
    la      x3, k_s1_l
    bn.sid  x2, 0(x3)

    li      x2, 23
    la      x3, k_s1_h
    bn.sid  x2, 0(x3)

    li      x2, 8
    la      x3, k_l
    bn.sid  x2, 0(x3)

    li      x2, 9
    la      x3, k_h
    bn.sid  x2, 0(x3)

    ecall

.data
    .globl k_s0_l
    .balign 32
    k_s0_l:
    .zero 32

    .globl k_s0_h
    .balign 32
    k_s0_h:
    .zero 32

    .globl k_s1_l
    .balign 32
    k_s1_l:
    .zero 32

    .globl k_s1_h
    .balign 32
    k_s1_h:
    .zero 32

    .globl k_l
    .balign 32
    k_l:
    .zero 32

    .globl k_h
    .balign 32
    k_h:
    .zero 32
