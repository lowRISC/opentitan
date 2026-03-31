/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Randomized test to verify the A2B conversion. */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x2, _params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  bn.not w2, w31 /* flag */
  bn.shv.8s w3, w2 >> 10 /* mask */

  /* Generate 100 random arithmetically shared vectors and verify that they can
     be correctly converted to Boolean shares. */
  loopi 100, 10
    /* Random vector of coefficients < q. */
    bn.wsrr w4, URND
    bn.and w4, w4, w3

    /* Random coefficient masks < q. */
    bn.wsrr w5, URND
    bn.and w5, w5, w3

    /* Create the two arithmetic shares and trigger the conversion. */
    bn.subvm.8s w0, w4, w5
    bn.mov w1, w5
    jal x1, sec_a2b_8x32

    /* Unmask the result. */
    bn.xor w0, w0, w1

    /* Check that the unmask result is equal to the initial vector. */
    bn.cmp w0, w4, FG0
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
