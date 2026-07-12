/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Test ML-KEM polynomial modular subtraction. */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  /* Load Q = 3329 and MU = 3327 into MOD register. */
  la x2, _params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  la x2, _poly_sub_a_base
  la x3, _poly_sub_b_base
  la x4, _poly_sub_c_base
  jal x1, poly_sub

  la x2, _poly_sub_a_underflow
  la x3, _poly_sub_b_underflow
  la x4, _poly_sub_c_underflow
  jal x1, poly_sub

  ecall

.data
.balign 32

_params:
.word 0x00000d01 /* q = 3329 */
.word 0x00000cff /* mu = 3327 */
.word 0x00000ce7 /* f = 3303 */
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000

_poly_sub_a_base:
.zero 1024
_poly_sub_b_base:
.zero 1024
_poly_sub_c_base:
.zero 1024

_poly_sub_a_underflow:
.zero 1024
_poly_sub_b_underflow:
.zero 1024
_poly_sub_c_underflow:
.zero 1024
