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
  la x2, _check_infinity_norm_z_z_good
  la x3, _check_infinity_norm_z_bound
  jal x1, check_infinity_norm_z

  la x2, _check_infinity_norm_z_res_good
  bn.sid x0, 0(x2)

  /* Unsuccessful inifinity norm check. */
  la x2, _check_infinity_norm_z_z_bad
  la x3, _check_infinity_norm_z_bound
  jal x1, check_infinity_norm_z

  bn.not w0, w0
  la x2, _check_infinity_norm_z_res_bad
  bn.sid x0, 0(x2)

  ecall

.data
.balign 32

/* 2^19 - BETA = 2^19 - 120. */
_check_infinity_norm_z_bound:
.word 0x0007ff88
.word 0x0007ff88
.word 0x0007ff88
.word 0x0007ff88
.word 0x0007ff88
.word 0x0007ff88
.word 0x0007ff88
.word 0x0007ff88

/*
 * q  = 8380417 = 2^23 - 2^13 + 1 (ML-DSA modulus)
 * mu = -q^-1 mod R (Montgomery constant)
 * f  = 256^-1 * R mod q (INTT divisor in Montgomery domain)
 */
_params:
.word 0x007fe001 /* q */
.word 0xfc7fdfff /* mu */
.word 0x00003ffe /* f */
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000

_stack:
.zero 4

.section .scratchpad
.balign 32

_check_infinity_norm_z_z_good:
.zero 7168
_check_infinity_norm_z_z_bad:
.zero 7168

_check_infinity_norm_z_res_good:
.zero 32
_check_infinity_norm_z_res_bad:
.zero 32
