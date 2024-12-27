/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
    OBTN.LOAD_INTEGRITY FI Penetration Test
*/
.section .text.start

    /* Execute 10 NOPs. */
    li x1, 10
    loop x1, 1
      nop

    ecall

.data
    /* Reference values. */
    .balign 32
    .globl refval1
    refval1:
      .word 0x1BADB002

    .balign 32
    .globl refval2
    refval2:
      .word 0x8BADF00D

    .balign 32
    .globl refval3
    refval3:
      .word 0xA5A5A5A5
