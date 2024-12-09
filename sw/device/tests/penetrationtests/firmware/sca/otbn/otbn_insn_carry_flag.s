/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
    OBTN.INSN.CARRY_FLAG SCA Test
*/
.section .text.start

    /* w3 & w10 are random, w10 contains the value big_num. */
    bn.wsrr w0, URND
    bn.wsrr w3, URND
    li      x10, 10
    la      x1, big_num
    bn.lid  x10, 0x00(x1)
    /* Load big_num_out base address */
    la      x1, big_num_out

    loopi 10, 1
      nop

    /* Add with carry: big_num = big_num + big_num. */
    bn.addc w10, w10, w10

    loopi 10, 1
      nop

    li      x2, 2
    bn.movr x2, x10
    /* If carry was set, store random number into w0. If not, store big_num.  */
    bn.sel  w0, w2, w3, C

    /* Write w0 back to DEM. */
    bn.sid  x0, 0x000(x1)

    ecall

.data
    .globl big_num
    .balign 32
    big_num:
        .zero 32

    .globl big_num_out
    .balign 32
    big_num_out:
        .zero 32
