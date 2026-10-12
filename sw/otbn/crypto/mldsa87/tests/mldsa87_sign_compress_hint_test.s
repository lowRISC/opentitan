/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Test that we can correcty compress the hint vector H. */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x2, _params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  la x2, _compress_hint_h_input0
  la x3, _compress_hint_h_output
  la x4, _compress_hint_slot
  jal x1, compress_hint

  ecall

.data
.balign 32

_compress_hint_h_input0:
.zero 1024
_compress_hint_h_input1:
.zero 1024
_compress_hint_h_input2:
.zero 1024
_compress_hint_h_input3:
.zero 1024
_compress_hint_h_input4:
.zero 1024
_compress_hint_h_input5:
.zero 1024
_compress_hint_h_input6:
.zero 1024
_compress_hint_h_input7:
.zero 1024

_compress_hint_h_output:
.zero 83
.zero 13 /* Padding */

_compress_hint_slot:
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
