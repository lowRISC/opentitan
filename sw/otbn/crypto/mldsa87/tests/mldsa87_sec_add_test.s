/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Randomized test to verify the secure addition. */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x2, _params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  bn.not w4, w31 /* flag */

  /* Generate 100 random Boolean-shared summands and verify that they can be
     correctly added together. */
  loopi 100, 13
    /* Random vectors x and y < 2^32. */
    bn.wsrr w5, URND
    bn.wsrr w6, URND

    /* Expected result x + y mod 2^32. */
    bn.addv.8s w7, w5, w6

    /* Random masks */
    bn.wsrr w8, URND
    bn.wsrr w9, URND

    /* Create the two Boolean shares and trigger the conversion. */
    bn.xor w0, w5, w8
    bn.mov w1, w8
    bn.xor w2, w6, w9
    bn.mov w3, w9
    jal x1, sec_add_8x32

    /* Unmask the result. */
    bn.xor w0, w0, w1

    /* Check that the unmask result is equal to the initial vector. */
    bn.cmp w0, w7, FG0
    bn.sel w4, w4, w31, FG0.Z
    /* End of loop */

  ecall

.data
.balign 32

_params:
.word 0x007fe001 /* q */
.word 0xfc7fdfff /* mu */
.word 0x0000a3fa /* n^-1 * R^3 mod q */
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000

_stack:
.zero 4
