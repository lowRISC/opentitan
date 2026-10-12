/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Verify that the we can correctly sample the S1 vector. */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x2, _params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  la x2, _expand_s1_rho_prime_share0
  la x3, _expand_s1_rho_prime_share1
  la x4, _expand_s1_s10_share0
  la x5, _expand_s1_s10_share1
  addi x6, x0, 0 /* r */
  loopi 7, 4
    jal x1, expand_s1
    addi x4, x4, 1024
    addi x5, x5, 1024
    addi x6, x6, 1
    /* End of loop */

   /* Unmask the sampled S1 polynomial */
  la x20, _expand_s1_s10_share0
  la x21, _expand_s1_s10_share1
  addi x22, x0, 224
  jal x1, unmask_arithmetic

  ecall

.data
.balign 32

_expand_s1_rho_prime_share0:
.zero 96
_expand_s1_rho_prime_share1:
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

_expand_s1_s10_share0:
.zero 1024
_expand_s1_s11_share0:
.zero 1024
_expand_s1_s12_share0:
.zero 1024
_expand_s1_s13_share0:
.zero 1024
_expand_s1_s14_share0:
.zero 1024
_expand_s1_s15_share0:
.zero 1024
_expand_s1_s16_share0:
.zero 1024

_expand_s1_s10_share1:
.zero 1024
_expand_s1_s11_share1:
.zero 1024
_expand_s1_s12_share1:
.zero 1024
_expand_s1_s13_share1:
.zero 1024
_expand_s1_s14_share1:
.zero 1024
_expand_s1_s15_share1:
.zero 1024
_expand_s1_s16_share1:
.zero 1024
