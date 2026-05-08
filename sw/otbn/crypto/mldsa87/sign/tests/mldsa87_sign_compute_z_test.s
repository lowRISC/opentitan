/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Test that we can correctly compute the signature vector Z and check its
   infinity norm. */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x2, _params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  /*
   * First, execute the negative test where the derived vector fails the
   * infinity norm check.
   */

  la x2, _compute_z_rho_prime_share0_neg
  la x3, _compute_z_rho_prime_share1_neg
  la x4, _compute_z_c_neg
  la x5, _compute_z_s1_share0_neg
  la x6, _compute_z_s1_share1_neg
  la x7, _compute_z_bound
  la x8, _compute_z_z0
  la x9, _compute_z_slot0
  la x10, _compute_z_slot1
  la x11, _compute_z_slot2
  la x12, _compute_z_slot3
  jal x1, compute_z

  bn.not w0, w0
  la x2, _compute_z_res_neg
  bn.sid x0, 0(x2)

  /*
   * Second, execute the positive test where the derived vector passes the
   * infinity norm check.
   */

  la x2, _compute_z_rho_prime_share0_pos
  la x3, _compute_z_rho_prime_share1_pos
  la x4, _compute_z_c_pos
  la x5, _compute_z_s1_share0_pos
  la x6, _compute_z_s1_share1_pos
  la x7, _compute_z_bound
  la x8, _compute_z_z0
  la x9, _compute_z_slot0
  la x10, _compute_z_slot1
  la x11, _compute_z_slot2
  la x12, _compute_z_slot3
  jal x1, compute_z

  la x2, _compute_z_res_pos
  bn.sid x0, 0(x2)

  ecall

.data
.balign 32

/* Positive vectors. */
_compute_z_rho_prime_share0_pos:
.zero 96
_compute_z_rho_prime_share1_pos:
.zero 96
_compute_z_c_pos:
.zero 1024
_compute_z_s1_share0_pos:
.zero 672
_compute_z_s1_share1_pos:
.zero 672

/* Negative vectors. */
_compute_z_rho_prime_share0_neg:
.zero 96
_compute_z_rho_prime_share1_neg:
.zero 96
_compute_z_c_neg:
.zero 1024
_compute_z_s1_share0_neg:
.zero 672
_compute_z_s1_share1_neg:
.zero 672

_compute_z_bound:
.word 0x0007ff88
.word 0x0007ff88
.word 0x0007ff88
.word 0x0007ff88
.word 0x0007ff88
.word 0x0007ff88
.word 0x0007ff88
.word 0x0007ff88

_compute_z_res_pos:
.zero 32
_compute_z_res_neg:
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

_compute_z_z0:
.zero 1024
_compute_z_z1:
.zero 1024
_compute_z_z2:
.zero 1024
_compute_z_z3:
.zero 1024
_compute_z_z4:
.zero 1024
_compute_z_z5:
.zero 1024
_compute_z_z6:
.zero 1024

_compute_z_slot0:
.zero 1024
_compute_z_slot1:
.zero 1024
_compute_z_slot2:
.zero 1024
_compute_z_slot3:
.zero 1024
