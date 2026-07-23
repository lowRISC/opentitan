/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x2, _nonce
  lw x3, 0(x2)
  la x2, _s_seed
  la x4, _poly_out
  jal x1, expand_prf

  ecall

.data
.balign 32

_nonce:
.word 0

.balign 32
_s_seed:
.zero 64

.balign 32
_poly_out:
.zero 1024
