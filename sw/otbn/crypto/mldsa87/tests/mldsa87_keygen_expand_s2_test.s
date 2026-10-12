/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Verify that the we can correctly sample the S2 vector. */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x2, _params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  la x2, _expand_s2_rho_prime_share0
  la x3, _expand_s2_rho_prime_share1
  la x4, _expand_s2_s20_share0
  la x5, _expand_s2_s20_share1
  addi x6, x0, 0 /* r */
  loopi 8, 4
    jal x1, expand_s2
    addi x4, x4, 1024
    addi x5, x5, 1024
    addi x6, x6, 1
    /* End of loop */

   /* Unmask the sampled S2 polynomial */
  la x20, _expand_s2_s20_share0
  la x21, _expand_s2_s20_share1
  addi x22, x0, 256
  jal x1, unmask_arithmetic

  ecall

.data
.balign 32

_expand_s2_rho_prime_share0:
.zero 96
_expand_s2_rho_prime_share1:
.zero 96

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

.section .scratchpad
.balign 32

_expand_s2_s20_share0:
.zero 1024
_expand_s2_s21_share0:
.zero 1024
_expand_s2_s22_share0:
.zero 1024
_expand_s2_s23_share0:
.zero 1024
_expand_s2_s24_share0:
.zero 1024
_expand_s2_s25_share0:
.zero 1024
_expand_s2_s26_share0:
.zero 1024
_expand_s2_s27_share0:
.zero 1024

_expand_s2_s20_share1:
.zero 1024
_expand_s2_s21_share1:
.zero 1024
_expand_s2_s22_share1:
.zero 1024
_expand_s2_s23_share1:
.zero 1024
_expand_s2_s24_share1:
.zero 1024
_expand_s2_s25_share1:
.zero 1024
_expand_s2_s26_share1:
.zero 1024
_expand_s2_s27_share1:
.zero 1024
