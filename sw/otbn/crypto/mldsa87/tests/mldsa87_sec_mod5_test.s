/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Test that we can correctly compute a Boolean-masked modulo 5 operation. */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x2, _params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  la x2, _sec_mod5_x0_share0
  la x3, _sec_mod5_x0_share1
  la x4, _sec_mod5_y0

  addi x5, x0, 0
  addi x6, x0, 1

  /* Calculate x mod 5, for 8x8 coefficients. */
  loopi 8, 5
    bn.lid x5, 0(x2++)
    bn.lid x6, 0(x3++)

    jal x1, sec_mod5_8x32

    bn.xor w0, w0, w1 /* unmask */
    bn.sid x5, 0(x4++)
    /* End of loop */

  ecall

.data
.balign 32

_sec_mod5_x0_share0:
.zero 32
_sec_mod5_x1_share0:
.zero 32
_sec_mod5_x2_share0:
.zero 32
_sec_mod5_x3_share0:
.zero 32
_sec_mod5_x4_share0:
.zero 32
_sec_mod5_x5_share0:
.zero 32
_sec_mod5_x6_share0:
.zero 32
_sec_mod5_x7_share0:
.zero 32

_sec_mod5_x0_share1:
.zero 32
_sec_mod5_x1_share1:
.zero 32
_sec_mod5_x2_share1:
.zero 32
_sec_mod5_x3_share1:
.zero 32
_sec_mod5_x4_share1:
.zero 32
_sec_mod5_x5_share1:
.zero 32
_sec_mod5_x6_share1:
.zero 32
_sec_mod5_x7_share1:
.zero 32

_sec_mod5_y0:
.zero 32
_sec_mod5_y1:
.zero 32
_sec_mod5_y2:
.zero 32
_sec_mod5_y3:
.zero 32
_sec_mod5_y4:
.zero 32
_sec_mod5_y5:
.zero 32
_sec_mod5_y6:
.zero 32
_sec_mod5_y7:
.zero 32

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
.zero 256
