/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x10, _const_params
  bn.lid x0, 0(x10)
  bn.wsrw 0x0, w0  /* 0x0 is MOD CSR */

  la x2, _rho
  addi x3, x0, 2  /* j = 2 */
  addi x4, x0, 1  /* i = 1 */
  la x5, _poly_out
  jal x1, expand_a

  ecall

.data
.balign 32

_rho:
.zero 64

_const_params:
.word 3329
.word 0x94570cff
.zero 24

_poly_out:
.zero 1024
