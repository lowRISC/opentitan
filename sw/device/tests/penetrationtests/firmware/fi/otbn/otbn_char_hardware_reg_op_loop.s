/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
    OBTN.CHAR.HARDWARE_REG_OP_LOOP FI Penetration Test
*/
.section .text.start

    /* Init x2 with number of iterations (100) for the outer hardware loop. */
    li  x2, 100
    /* Init loop counter (x3) register. */
    li  x3, 0
    /* Use nested hardware loops too increment x3 10000 times by 1. */
    loop x2, 3
      loopi 100, 1
        addi x3, x3, 1
      nop

    /* Store result. */
    la x4, lc
    sw x3, 0(x4)

    ecall
  .data

    /* Loop counter (lc) result. */
    .balign 32
    .globl lc
    lc:
    .zero 32
