/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  /* Load Q = 3329 and MU = 3327 into MOD register. */
  la x2, _params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  la x2, _poly_in
  jal x1, ntt

  la x2, _poly_in
  la x3, _poly_out
  li x4, 32
_copy_ntt_out:
  bn.lid x0, 0(x2++)
  bn.sid x0, 0(x3++)
  addi x4, x4, -1
  bne  x4, x0, _copy_ntt_out

  ecall


.data
.balign 32

_params:
.word 0x00000d01 /* q = 3329 */
.word 0x94570cff /* mu = -q^-1 mod 2^32 */
.word 0x00000ce7 /* f = 3303 */
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000

_poly_in:
.zero 1024

_poly_out:
.zero 1024
