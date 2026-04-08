/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Test we can correctly multiply a 320-bit scalar and a 128-bit scalar. */

.section .text.start

main:
  bn.xor w31, w31, w31

  jal x1, sc_init

  /* [w21, w20] <= x. */
  li x2, 20
  la x3, _sc_mul_320x128_x
  bn.lid x2++, 0(x3)
  bn.lid x2++, 32(x3)

  /* w22 <= y. */
  la x3, _sc_mul_320x128_y
  bn.lid x2++, 0(x3)

  /* w18 <= x * y mod L. */
  jal x1, sc_mul_320x128

  ecall

.data
.balign 32

_sc_mul_320x128_x:
.zero 64
_sc_mul_320x128_y:
.zero 32
