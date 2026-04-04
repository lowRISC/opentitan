/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Check that the `SecBoundCheck` gadget is correct. */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x2, _params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  la x2, _sec_bound_check_x0_pos
  la x3, _sec_bound_check_x1_pos
  la x4, _sec_bound_check_b
  jal x1, sec_bound_check

  la x2, _sec_bound_check_res_pos
  bn.sid x0, 0(x2)

  la x2, _sec_bound_check_x0_neg
  la x3, _sec_bound_check_x1_neg
  la x4, _sec_bound_check_b
  jal x1, sec_bound_check

  la x2, _sec_bound_check_res_neg
  bn.not w0, w0
  bn.sid x0, 0(x2)

  ecall

.data
.balign 32

_params:
.word 0x007fe001 /* q */
.word 0xfc7fdfff /* mu */
.word 0x0000a3fa /* n^-1 * R^3 mod q */
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000

_sec_bound_check_x0_pos:
.zero 1024
_sec_bound_check_x1_pos:
.zero 1024
_sec_bound_check_x0_neg:
.zero 1024
_sec_bound_check_x1_neg:
.zero 1024

_sec_bound_check_res_pos:
.zero 32
_sec_bound_check_res_neg:
.zero 32

/* The bound b = GAMMA1 - BETA = 2^19 - 120. */
_sec_bound_check_b:
.word 0x0007ff88
.word 0x0007ff88
.word 0x0007ff88
.word 0x0007ff88
.word 0x0007ff88
.word 0x0007ff88
.word 0x0007ff88
.word 0x0007ff88

_stack:
.zero 4
