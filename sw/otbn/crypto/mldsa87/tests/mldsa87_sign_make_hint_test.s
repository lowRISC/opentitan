/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Test that we can correcty compute the hint vector H. */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x2, _params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  la x2, _make_hint_x0_0
  la x3, _make_hint_w1_enc
  la x4, _make_hint_slot
  jal x1, make_hint

  ecall

.data
.balign 32

_make_hint_x0_0:
.zero 1024
_make_hint_x0_1:
.zero 1024
_make_hint_x0_2:
.zero 1024
_make_hint_x0_3:
.zero 1024
_make_hint_x0_4:
.zero 1024
_make_hint_x0_5:
.zero 1024
_make_hint_x0_6:
.zero 1024
_make_hint_x0_7:
.zero 1024

_make_hint_w1_enc:
.zero 1024

_make_hint_slot:
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
