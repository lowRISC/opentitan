/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
    OBTN.INSN.COMBI_OPS SCA Test
*/
.section .text.start

    /* Load results base addresses */
    la      x1, result_1
    la      x2, result_2
    la      x3, result_3
    la      x4, result_4
    la      x5, result_5
    la      x6, result_6
    la      x7, result_7
    la      x8, result_8

    /* Load first input in w0 */
    la      x9, big_input_1
    bn.lid  x0, 0x00(x9)

    /* Load second input in w1 */
    li      x10, 1
    la      x9, big_input_2
    bn.lid  x10, 0x00(x9)

    /* Set the zero register */
    bn.xor w31, w31, w31

    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop

    /* Copy paste each value 8 times */
    bn.rshi  w2, w0, w31 >> 224
    bn.xor   w0, w0, w2
    bn.rshi  w2, w0, w31 >> 192
    bn.xor   w0, w0, w2
    bn.rshi  w2, w0, w31 >> 128
    bn.xor   w0, w0, w2

    bn.rshi  w2, w1, w31 >> 224
    bn.xor   w1, w1, w2
    bn.rshi  w2, w1, w31 >> 192
    bn.xor   w1, w1, w2
    bn.rshi  w2, w1, w31 >> 128
    bn.xor   w1, w1, w2

    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop

    /* Move w0 around */
    bn.mov w10, w0
    bn.mov w11, w0
    bn.mov w12, w0
    bn.mov w13, w0
    bn.mov w14, w0

    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop

    /* Add the two values */
    bn.add w15, w0, w1
    bn.add w16, w0, w1
    bn.add w17, w0, w1
    bn.add w18, w0, w1
    bn.add w19, w0, w1

    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop

    /* Subtract the two values */
    bn.sub w20, w0, w1
    bn.sub w21, w0, w1
    bn.sub w22, w0, w1
    bn.sub w23, w0, w1
    bn.sub w24, w0, w1


    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop

    /* Xor the two values */
    bn.xor w25, w0, w1
    bn.xor w26, w0, w1
    bn.xor w27, w0, w1
    bn.xor w28, w0, w1
    bn.xor w29, w0, w1

    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop

    /* Clear some registers */
    bn.xor w10, w10, w10
    bn.xor w11, w11, w11
    bn.xor w12, w12, w12
    bn.xor w13, w13, w13

    bn.xor w15, w15, w15
    bn.xor w16, w16, w16
    bn.xor w17, w17, w17
    bn.xor w18, w18, w18

    bn.xor w20, w20, w20
    bn.xor w21, w21, w21
    bn.xor w22, w22, w22
    bn.xor w23, w23, w23

    bn.xor w25, w25, w25
    bn.xor w26, w26, w26
    bn.xor w27, w27, w27
    bn.xor w28, w28, w28

    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop

    /* Left shift the value by one */
    bn.rshi w4, w0, w31 >> 255
    bn.rshi w5, w0, w31 >> 255
    bn.rshi w6, w0, w31 >> 255
    bn.rshi w7, w0, w31 >> 255
    bn.rshi w8, w0, w31 >> 255

    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop

    /* Multiply the two values */
    bn.mulqacc.so w9.L, w0.0, w1.0, 0
    bn.mulqacc.so w10.L, w0.0, w1.0, 0
    bn.mulqacc.so w11.L, w0.0, w1.0, 0
    bn.mulqacc.so w12.L, w0.0, w1.0, 0
    bn.mulqacc.so w13.L, w0.0, w1.0, 0

    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop

    /* Compare the two values */
    bn.cmp w0, w1
    bn.cmp w0, w1
    bn.cmp w0, w1
    bn.cmp w0, w1
    bn.cmp w0, w1

    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop

    /* Write back to results */
    bn.sid  x0, 0x000(x1)

    addi    x20, x0, 14
    bn.sid  x20, 0x000(x2)

    addi    x21, x0, 19
    bn.sid  x21, 0x000(x3)

    addi    x22, x0, 24
    bn.sid  x22, 0x000(x4)

    addi    x23, x0, 29
    bn.sid  x23, 0x000(x5)

    addi    x24, x0, 8
    bn.sid  x24, 0x000(x6)

    addi    x25, x0, 13
    bn.sid  x25, 0x000(x7)

    la x17, result_8
    csrrs x16, FG0, x0
    sw  x16, 0(x17)

    ecall

.data
    .globl big_input_1
    .balign 32
    big_input_1:
        .zero 32

    .globl big_input_2
    .balign 32
    big_input_2:
        .zero 32

    .globl result_1
    .balign 32
    result_1:
        .zero 32

    .globl result_2
    .balign 32
    result_2:
        .zero 32

    .globl result_3
    .balign 32
    result_3:
        .zero 32

    .globl result_4
    .balign 32
    result_4:
        .zero 32

    .globl result_5
    .balign 32
    result_5:
        .zero 32

    .globl result_6
    .balign 32
    result_6:
        .zero 32

    .globl result_7
    .balign 32
    result_7:
        .zero 32

    .globl result_8
    .balign 4
    result_8:
        .zero 4
