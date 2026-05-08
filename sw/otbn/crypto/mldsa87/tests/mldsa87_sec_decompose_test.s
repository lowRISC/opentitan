/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Check that the `SecDecompose` gadget is correct. */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x2, _params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  la x2, _sec_decompose_w_s0
  la x3, _sec_decompose_w_s1
  la x4, _sec_decompose_w1
  jal x1, sec_decompose

  addi x20, x2, 0
  addi x21, x3, 0
  addi x22, x0, 32
  jal x1, unmask_arithmetic

  ecall

.data
.balign 32

_sec_decompose_w_s0:
.zero 1024
_sec_decompose_w_s1:
.zero 1024
_sec_decompose_w1:
.zero 1024

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
