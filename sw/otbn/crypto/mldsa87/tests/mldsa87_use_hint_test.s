/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Test that the hint can be correctly applied to W_approx. */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x2, _params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  la x2, _use_hint_w
  la x3, _use_hint_h_enc
  la x4, _use_hint_slot0
  la x5, _use_hint_slot1
  jal x1, use_hint

  ecall

.data
.balign 32

_use_hint_h_enc:
.zero 332
.zero 20 /* Padding */

_use_hint_w:
.zero 8192

_use_hint_slot0:
.zero 1024
_use_hint_slot1:
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
