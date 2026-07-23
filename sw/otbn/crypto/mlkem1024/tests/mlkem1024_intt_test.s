/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.globl main

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  /* Initialize MOD register with Q = 3329, MU = 0x94570CFF */
  la x2, _params
  bn.lid x0, 0(x2)
  bn.wsrw 0, w0

  la x2, _poly_in
  la x3, _poly_out
  jal x1, intt

  ecall

.section .data
.balign 32

_params:
.word 0x00000d01 /* q = 3329 */
.word 0x94570cff /* mu = -q^-1 mod 2^32 */
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000

_poly_in:
.zero 1024

_poly_out:
.zero 1024
