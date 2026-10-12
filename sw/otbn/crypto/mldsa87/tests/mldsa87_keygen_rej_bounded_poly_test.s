/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Verify that the we can correctly sample a masked S{1,2} polynomial. */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x2, _params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  la x2, _rej_bounded_poly_rho_prime_share0
  la x3, _rej_bounded_poly_rho_prime_share1
  la x4, _rej_bounded_poly_s_share0
  la x5, _rej_bounded_poly_s_share1
  jal x1, rej_bounded_poly

   /* Unmask the sampled S polynomial */
  la x20, _rej_bounded_poly_s_share0
  la x21, _rej_bounded_poly_s_share1
  addi x22, x0, 32
  jal x1, unmask_arithmetic

  ecall

.data
.balign 32

_rej_bounded_poly_rho_prime_share0:
.zero 64
.zero 32
_rej_bounded_poly_rho_prime_share1:
.zero 64
.zero 32

_rej_bounded_poly_s_share0:
.zero 1024
_rej_bounded_poly_s_share1:
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
