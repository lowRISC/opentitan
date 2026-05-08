/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Test that we can correctly decode the secret-key polynomials s{1, 2}. */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x2, _params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  la x2, _decode_s_s_enc_share0
  la x3, _decode_s_s_enc_share1
  la x4, _decode_s_s_dec_share0
  la x5, _decode_s_s_dec_share1
  jal x1, decode_s

  la x20, _decode_s_s_dec_share0
  la x21, _decode_s_s_dec_share1
  addi x22, x0, 32
  jal x1, unmask_arithmetic

  ecall

.data
.balign 32

_decode_s_s_enc_share0:
.zero 96
_decode_s_s_enc_share1:
.zero 96

_decode_s_s_dec_share0:
.zero 1024
_decode_s_s_dec_share1:
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
