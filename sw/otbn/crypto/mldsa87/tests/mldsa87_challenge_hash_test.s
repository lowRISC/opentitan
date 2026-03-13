/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Test that we can correctly compute the challenge hash. */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x2, _challenge_hash_mu
  la x3, _challenge_hash_w1_enc
  la x4, _challenge_hash_c
  jal x1, challenge_hash

  ecall

.data
.balign 32

_challenge_hash_mu:
.zero 64
_challenge_hash_w1_enc:
.zero 1024
_challenge_hash_c:
.zero 64

_stack:
.zero 4
