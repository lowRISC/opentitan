/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Test that the polynomial modular addition is correct. */

.section .text.start

main:
  /* Setup stack pointer and all-zero WDR. */
  la x31, _stack
  bn.xor w31, w31, w31

  /* Load the parameters into the MOD WSR. */
  la x2, _params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  la x2, _poly_add_a_base
  la x3, _poly_add_b_base
  la x4, _poly_add_c_base
  jal x1, poly_add

  la x2, _poly_add_a_overflow
  la x3, _poly_add_b_overflow
  la x4, _poly_add_c_overflow
  jal x1, poly_add

  ecall

.data
.balign 32

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

_poly_add_a_base:
.zero 1024
_poly_add_b_base:
.zero 1024
_poly_add_c_base:
.zero 1024

_poly_add_a_overflow:
.zero 1024
_poly_add_b_overflow:
.zero 1024
_poly_add_c_overflow:
.zero 1024

_stack:
.zero 4
