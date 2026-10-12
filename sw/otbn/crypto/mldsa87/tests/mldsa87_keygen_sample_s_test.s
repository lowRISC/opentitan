/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Verify that the we can correctly sample the S{1, 2} vectors. */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x2, _params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  la x2, _sample_s_rho_prime_share0
  la x3, _sample_s_rho_prime_share1
  la x4, _sample_s_s1_enc_share0
  la x5, _sample_s_s1_enc_share1
  la x6, _sample_s_s2_enc_share0
  la x7, _sample_s_s2_enc_share1
  la x8, _sample_s_slot0
  la x9, _sample_s_slot1
  jal x1, sample_s

  la x20, _sample_s_s1_enc_share0
  la x21, _sample_s_s1_enc_share1
  addi x22, x0, 21
  jal x1, unmask_boolean

  la x20, _sample_s_s2_enc_share0
  la x21, _sample_s_s2_enc_share1
  addi x22, x0, 24
  jal x1, unmask_boolean

  ecall

.data
.balign 32

_sample_s_rho_prime_share0:
.zero 66
.zero 30 /* Padding */
_sample_s_rho_prime_share1:
.zero 66
.zero 30 /* Padding */

_sample_s_s1_enc_share0:
.zero 672
_sample_s_s1_enc_share1:
.zero 672
_sample_s_s2_enc_share0:
.zero 768
_sample_s_s2_enc_share1:
.zero 768

_sample_s_slot0:
.zero 1024
_sample_s_slot1:
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
