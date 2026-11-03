/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Verify that the we can correctly compute the T vector. */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x2, _params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  la x2, _compute_t_rho
  la x3, _compute_t_s1_enc_share0
  la x4, _compute_t_s1_enc_share1
  la x5, _compute_t_s2_enc_share0
  la x6, _compute_t_s2_enc_share1
  la x7, _compute_t_t0_share0
  la x8, _compute_t_t0_share1
  la x9, _compute_t_slot0
  la x10, _compute_t_slot1
  la x11, _compute_t_slot2
  jal x1, compute_t

  la x20, _compute_t_t0_share0
  la x21, _compute_t_t0_share1
  addi x22, x0, 256
  jal x1, unmask_arithmetic

  ecall

.data
.balign 32

_compute_t_rho:
.zero 34
.zero 30 /* Padding */

_compute_t_s1_enc_share0:
.zero 672
_compute_t_s1_enc_share1:
.zero 672
_compute_t_s2_enc_share0:
.zero 768
_compute_t_s2_enc_share1:
.zero 768

_compute_t_slot0:
.zero 1024
_compute_t_slot1:
.zero 1024
_compute_t_slot2:
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

.section .scratchpad

_compute_t_t0_share0:
.zero 1024
_compute_t_t1_share0:
.zero 1024
_compute_t_t2_share0:
.zero 1024
_compute_t_t3_share0:
.zero 1024
_compute_t_t4_share0:
.zero 1024
_compute_t_t5_share0:
.zero 1024
_compute_t_t6_share0:
.zero 1024
_compute_t_t7_share0:
.zero 1024

_compute_t_t0_share1:
.zero 1024
_compute_t_t1_share1:
.zero 1024
_compute_t_t2_share1:
.zero 1024
_compute_t_t3_share1:
.zero 1024
_compute_t_t4_share1:
.zero 1024
_compute_t_t5_share1:
.zero 1024
_compute_t_t6_share1:
.zero 1024
_compute_t_t7_share1:
.zero 1024
