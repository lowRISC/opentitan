/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Test that the infinity norm check is computed correctly. */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x2, _params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  /* Successful infinity norm check. */
  la x2, _check_infinity_norm_poly_good
  la x3, _check_infinity_norm_bound
  jal x1, check_infinity_norm

  la x2, _check_infinity_norm_res_good
  bn.sid x0, 0(x2)

  /* Unsuccessful inifinity norm check. */
  la x2, _check_infinity_norm_poly_bad
  la x3, _check_infinity_norm_bound
  jal x1, check_infinity_norm

  bn.not w0, w0
  la x2, _check_infinity_norm_res_bad
  bn.sid x0, 0(x2)

  ecall

.data
.balign 32

/* 2^19 - BETA = 2^19 - 120. */
_check_infinity_norm_bound:
.word 0x0007ff88
.word 0x0007ff88
.word 0x0007ff88
.word 0x0007ff88
.word 0x0007ff88
.word 0x0007ff88
.word 0x0007ff88
.word 0x0007ff88

_check_infinity_norm_poly_good:
.zero 1024
_check_infinity_norm_poly_bad:
.zero 1024

_check_infinity_norm_res_good:
.zero 32
_check_infinity_norm_res_bad:
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
.zero 4
