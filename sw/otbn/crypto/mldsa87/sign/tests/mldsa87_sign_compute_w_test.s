/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Test that we can correctly compute the commitment vector W. */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x2, _params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  la x2, _compute_w_w0_share0
  la x3, _compute_w_w0_share1
  la x4, _compute_w_rho
  la x5, _compute_w_rho_prime_share0
  la x6, _compute_w_rho_prime_share1
  la x7, _compute_w_slot0
  la x8, _compute_w_slot1
  la x9, _compute_w_slot2
  jal x1, compute_w

  la x20, _compute_w_w0_share0
  la x21, _compute_w_w0_share1
  addi x22, x0, 256
  jal x1, unmask_arithmetic

  ecall

.data
.balign 32

_compute_w_rho:
.zero 64

_compute_w_rho_prime_share0:
.zero 96
_compute_w_rho_prime_share1:
.zero 96

_compute_w_slot0:
.zero 1024
_compute_w_slot1:
.zero 1024
_compute_w_slot2:
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

_compute_w_w0_share0:
.zero 1024
_compute_w_w1_share0:
.zero 1024
_compute_w_w2_share0:
.zero 1024
_compute_w_w3_share0:
.zero 1024
_compute_w_w4_share0:
.zero 1024
_compute_w_w5_share0:
.zero 1024
_compute_w_w6_share0:
.zero 1024
_compute_w_w7_share0:
.zero 1024
_compute_w_w0_share1:
.zero 1024
_compute_w_w1_share1:
.zero 1024
_compute_w_w2_share1:
.zero 1024
_compute_w_w3_share1:
.zero 1024
_compute_w_w4_share1:
.zero 1024
_compute_w_w5_share1:
.zero 1024
_compute_w_w6_share1:
.zero 1024
_compute_w_w7_share1:
.zero 1024
