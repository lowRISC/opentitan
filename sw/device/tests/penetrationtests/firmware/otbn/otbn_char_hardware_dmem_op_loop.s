/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
    OBTN.CHAR.HARDWARE_DMEM_OP_LOOP FI Penetration Test
*/
.section .text.start

    /* Load loop counter from dmem and set num it. of outer loop to 100. */
    li x1, 100
    la x3, lc
    /* Increment loop counter in nested hardware loops. */
    loop x1, 5
      loopi 100, 3
        lw x2, 0(x3)
        addi x2, x2, 1
        sw x2, 0(x3)
      nop

    ecall

.data
    /* Loop counter (lc) result. */
    .balign 32
    .globl lc
    lc:
    .zero 32
