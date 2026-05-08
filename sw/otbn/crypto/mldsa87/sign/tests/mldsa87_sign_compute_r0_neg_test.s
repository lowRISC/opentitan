/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Test that that a R0 vector with invalid bound results in failure. Due to
   memory constraints this test is seperated from its positive counterpart. */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x2, _params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  la x2, _compute_r0_w0_share0
  la x3, _compute_r0_w0_share1
  la x4, _compute_r0_c
  la x5, _compute_r0_s2_share0
  la x6, _compute_r0_s2_share1
  la x7, _compute_r0_bound
  la x8, _compute_r0_slot0
  la x9, _compute_r0_slot1
  jal x1, compute_r0

  bn.not w0, w0
  la x2, _compute_r0_res
  bn.sid x0, 0(x2)

  ecall

.data
.balign 32

_compute_r0_c:
.zero 1024

_compute_r0_s2_share0:
.zero 768
_compute_r0_s2_share1:
.zero 768

_compute_r0_slot0:
.zero 1024
_compute_r0_slot1:
.zero 1024

_compute_r0_bound:
.word 0x0003fe88
.word 0x0003fe88
.word 0x0003fe88
.word 0x0003fe88
.word 0x0003fe88
.word 0x0003fe88
.word 0x0003fe88
.word 0x0003fe88

_compute_r0_res:
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

_compute_r0_w0_share0:
.zero 1024
_compute_r0_w1_share0:
.zero 1024
_compute_r0_w2_share0:
.zero 1024
_compute_r0_w3_share0:
.zero 1024
_compute_r0_w4_share0:
.zero 1024
_compute_r0_w5_share0:
.zero 1024
_compute_r0_w6_share0:
.zero 1024
_compute_r0_w7_share0:
.zero 1024

_compute_r0_w0_share1:
.zero 1024
_compute_r0_w1_share1:
.zero 1024
_compute_r0_w2_share1:
.zero 1024
_compute_r0_w3_share1:
.zero 1024
_compute_r0_w4_share1:
.zero 1024
_compute_r0_w5_share1:
.zero 1024
_compute_r0_w6_share1:
.zero 1024
_compute_r0_w7_share1:
.zero 1024
