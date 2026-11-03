/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Test that we can verify the encoding of the hint. */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x2, _params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  /*
   * Valid hint:
   */

  la x2, _check_hint_h_enc_pos
  jal x1, check_hint

  la x2, _check_hint_res_pos
  bn.sid x0, 0(x2)

  /*
   * Invalid hint (fails condition 1):
   */

  la x2, _check_hint_h_enc_neg1
  jal x1, check_hint

  bn.not w0, w0
  la x2, _check_hint_res_neg1
  bn.sid x0, 0(x2)

  /*
   * Invalid hint (fails condition 2):
   */

  la x2, _check_hint_h_enc_neg2
  jal x1, check_hint

  bn.not w0, w0
  la x2, _check_hint_res_neg2
  bn.sid x0, 0(x2)

  /*
   * Invalid hint (fails condition 3):
   */

  la x2, _check_hint_h_enc_neg3
  jal x1, check_hint

  bn.not w0, w0
  la x2, _check_hint_res_neg3
  bn.sid x0, 0(x2)

  ecall

.data
.balign 32

_check_hint_h_enc_pos:
.zero 336
.zero 16 /* Padding */
_check_hint_h_enc_neg1:
.zero 336
.zero 16 /* Padding */
_check_hint_h_enc_neg2:
.zero 336
.zero 16 /* Padding */
_check_hint_h_enc_neg3:
.zero 336
.zero 16 /* Padding */

_check_hint_res_pos:
.zero 32
_check_hint_res_neg1:
.zero 32
_check_hint_res_neg2:
.zero 32
_check_hint_res_neg3:
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
