/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Test that we can correctly compute X0 = R0 + C * T0. */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x2, _params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  la x2, _compute_x0_0
  la x3, _compute_x0_c
  la x4, _compute_x0_t0_enc
  la x5, _compute_x0_slot
  jal x1, compute_x0

  ecall

.data
.balign 32

_compute_x0_0:
.zero 1024
_compute_x0_1:
.zero 1024
_compute_x0_2:
.zero 1024
_compute_x0_3:
.zero 1024
_compute_x0_4:
.zero 1024
_compute_x0_5:
.zero 1024
_compute_x0_6:
.zero 1024
_compute_x0_7:
.zero 1024

_compute_x0_c:
.zero 1024

_compute_x0_t0_enc:
.zero 3328

_compute_x0_slot:
.zero 1024

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
