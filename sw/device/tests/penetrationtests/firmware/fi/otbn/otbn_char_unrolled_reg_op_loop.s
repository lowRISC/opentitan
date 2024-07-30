/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
    OBTN.CHAR.UNROLLED_REG_OP_LOOP FI Penetration Test
*/
.section .text.start

    /* Init loop counter (x2) register and increment 100 times. */
    li  x2, 0
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1
    addi x2, x2, 1

    /* Store result. */
    la x3, lc
    sw x2, 0(x3)

    ecall
.data

    /* Loop counter (lc) result. */
    .balign 32
    .globl lc
    lc:
    .zero 32
