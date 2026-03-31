/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Randomized test to verify the secure Boolean unmasking. */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x2, _params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  bn.not w2, w31 /* flag */

  /* Generate 100 random Boolean-shared vectors and verify that they can be
     correctly unmasked. */
  loopi 100, 7
    /* Random vector. */
    bn.wsrr w3, URND

    /* Random masks. */
    bn.wsrr w4, URND

    /* Create the two Boolean shares and trigger the conversion. */
    bn.xor w0, w3, w4
    bn.mov w1, w4
    jal x1, sec_unmask_8x32

    /* Check that the unmask result is equal to the initial vector. */
    bn.cmp w0, w3, FG0
    bn.sel w2, w2, w31, FG0.Z
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
