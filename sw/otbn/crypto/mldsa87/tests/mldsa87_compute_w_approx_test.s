/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Test that we can correctly compute W_approx. */

.section .text.start

main:
  /* Setup stack pointer and all-zero WDR. */
  la x31, _stack
  bn.xor w31, w31, w31

  /* Load the parameters into the MOD WSR. */
  la x2, _params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  la x2, _compute_w_approx_rho
  la x3, _compute_w_approx_z
  la x4, _compute_w_approx_c
  la x5, _compute_w_approx_t1_enc
  la x6, _compute_w_approx_w_approx
  la x7, _compute_w_approx_slot
  jal x1, compute_w_approx

  ecall

.data
.balign 32

_compute_w_approx_rho:
.zero 64
_compute_w_approx_c:
.zero 1024
_compute_w_approx_t1_enc:
.zero 2560
_compute_w_approx_slot:
.zero 1024

/*
 * q  = 8380417 = 2^23 - 2^13 + 1 (ML-DSA modulus)
 * mu = -q^-1 mod R (Montgomery constant)
 * f  = 256^-1 * R^2 mod q (INTT divisor time R in Montgomery domain)
 */
_params:
.word 0x007fe001 /* q */
.word 0xfc7fdfff /* mu */
.word 0x0000a3fa /* f */
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000

_stack:
.zero 4

.section .scratchpad
.balign 32

_compute_w_approx_z:
.zero 7168
_compute_w_approx_w_approx:
.zero 8192
