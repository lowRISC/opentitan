/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Test we can correctly arithmetically share a scalar. */

.section .text.start

main:
  bn.xor w31, w31, w31

  jal x1, sc_init

  /* [w21, w20] <= x0_B. */
  li x2, 20
  la x3, _share_scalar_x0
  bn.lid x2++, 0(x3)
  bn.lid x2++, 32(x3)

  /* [w11, w10] <= x1_B. */
  li x2, 10
  la x3, _share_scalar_x1
  bn.lid x2++, 0(x3)
  bn.lid x2++, 32(x3)

  /* [w21, w20] <= x0_A. */
  /* [w10, w11] <= x1_A. */
  jal x1, share_scalar

  bn.mov w24, w20
  bn.mov w25, w21
  bn.mov w26, w10
  bn.mov w27, w11

  /* Set the upper 192 bits of both shares to 0. */
  bn.not w0, w31
  bn.rshi w0, w31, w0 >> 192
  bn.and w21, w21, w0
  bn.and w11, w11, w0

  /* /\* [w16, w17] <= x0_A + x1_A. *\/ */
  bn.add w16, w20, w10
  bn.addc w17, w21, w11

  /* /\* w18 <= x0_A + x0_A mod L. *\/ */
  jal x1, sc_reduce

  ecall

.data
.balign 32

_share_scalar_x0:
.zero 64
_share_scalar_x1:
.zero 64
