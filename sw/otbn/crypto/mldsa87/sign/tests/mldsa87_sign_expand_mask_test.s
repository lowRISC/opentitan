/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Test that we can correctly expand the polynomials of the mask vector Y. */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x2, _params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  la x2, _expand_mask_y0_share0
  la x3, _expand_mask_y0_share1
  la x4, _expand_mask_rho_prime_share0
  la x5, _expand_mask_rho_prime_share1
  addi x6, x0, 0 /* r */

  /* Sample all mask polynomials Y[r], 0 <= r < 7. */
  loopi 7, 4
    jal x1, expand_mask
    addi x2, x2, 1024
    addi x3, x3, 1024
    addi x6, x6, 1
    /* End of loop */

  la x20, _expand_mask_y0_share0
  la x21, _expand_mask_y0_share1
  addi x22, x0, 224
  jal x1, unmask_arithmetic

  ecall

.data
.balign 32

_expand_mask_rho_prime_share0:
.zero 96
_expand_mask_rho_prime_share1:
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

_expand_mask_y0_share0:
.zero 1024
_expand_mask_y1_share0:
.zero 1024
_expand_mask_y2_share0:
.zero 1024
_expand_mask_y3_share0:
.zero 1024
_expand_mask_y4_share0:
.zero 1024
_expand_mask_y5_share0:
.zero 1024
_expand_mask_y6_share0:
.zero 1024
_expand_mask_y0_share1:
.zero 1024
_expand_mask_y1_share1:
.zero 1024
_expand_mask_y2_share1:
.zero 1024
_expand_mask_y3_share1:
.zero 1024
_expand_mask_y4_share1:
.zero 1024
_expand_mask_y5_share1:
.zero 1024
_expand_mask_y6_share1:
.zero 1024
