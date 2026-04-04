/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Randomized test to verify the secure less-than-equal gadget. */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x2, _params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  addi x2, x0, 0
  addi x3, x0, 1
  addi x4, x0, 2

  la x5, _sec_leq_8x32_x0
  la x6, _sec_leq_8x32_x1
  la x7, _sec_leq_8x32_b
  la x8, _sec_leq_8x32_res

  loopi 32, 5
    bn.lid x2, 0(x5++)
    bn.lid x3, 0(x6++)
    bn.lid x4, 0(x7)

    jal x1, sec_leq_8x32

    bn.sid x0, 0(x8++)
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

/* b = 127. */
_sec_leq_8x32_b:
.word 0x0000007f
.word 0x0000007f
.word 0x0000007f
.word 0x0000007f
.word 0x0000007f
.word 0x0000007f
.word 0x0000007f
.word 0x0000007f

_sec_leq_8x32_x0:
.zero 1024
_sec_leq_8x32_x1:
.zero 1024

_sec_leq_8x32_res:
.zero 1024

_stack:
.zero 4
