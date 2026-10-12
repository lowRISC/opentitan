/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Test that we can correctly accept/rejects hint vectors based on their
   Hamming weight. */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x2, _params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  /* Positive test: */

  la x2, _hw_check_hint_h0_pos
  jal x1, hw_check_hint

  la x2, _hw_check_hint_res_pos
  bn.sid x0, 0(x2)

  /* Negative test: */

  la x2, _hw_check_hint_h0_neg
  jal x1, hw_check_hint

  bn.not w0, w0
  la x2, _hw_check_hint_res_neg
  bn.sid x0, 0(x2)

  ecall

.data
.balign 32

_hw_check_hint_res_pos:
.zero 32
_hw_check_hint_res_neg:
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

.section .scratchpad

_hw_check_hint_h0_pos:
.zero 1024
_hw_check_hint_h1_pos:
.zero 1024
_hw_check_hint_h2_pos:
.zero 1024
_hw_check_hint_h3_pos:
.zero 1024
_hw_check_hint_h4_pos:
.zero 1024
_hw_check_hint_h5_pos:
.zero 1024
_hw_check_hint_h6_pos:
.zero 1024
_hw_check_hint_h7_pos:
.zero 1024

_hw_check_hint_h0_neg:
.zero 1024
_hw_check_hint_h1_neg:
.zero 1024
_hw_check_hint_h2_neg:
.zero 1024
_hw_check_hint_h3_neg:
.zero 1024
_hw_check_hint_h4_neg:
.zero 1024
_hw_check_hint_h5_neg:
.zero 1024
_hw_check_hint_h6_neg:
.zero 1024
_hw_check_hint_h7_neg:
.zero 1024
