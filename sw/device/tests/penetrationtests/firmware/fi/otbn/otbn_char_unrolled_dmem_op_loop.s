/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
    OBTN.CHAR.UNROLLED_DMEM_OP_LOOP FI Penetration Test
*/
.section .text.start

    /* Load loop counter from dmem, increment, and store back. Do 100 times. */
    la x3, lc
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)
    lw x2, 0(x3)
    addi x2, x2, 1
    sw x2, 0(x3)

    ecall

.data
    /* Loop counter (lc) result. */
    .balign 32
    .globl lc
    lc:
    .zero 32
