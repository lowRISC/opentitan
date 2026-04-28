/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.section .text.start

main:
  bn.xor w31, w31, w31

  /* Set up for field arithmetic in preparation for scalar multiplication and
     point addition:
       MOD <= p
       w19 <= 19
       w30 <= 38. */
  jal x1, fe_init

  bn.not w1, w31 /* flag */

  /*
   * Positive test.
   */

  li x2, 10
  la x3, _ed25519_ext_is_on_curve_x_pos
  bn.lid x2++, 0(x3)
  bn.lid x2++, 32(x3)

  jal x1, ext_is_on_curve

  bn.sel w0, w1, w31, FG0.Z
  la x3, _ed25519_ext_is_on_curve_res_pos
  bn.sid x0, 0(x3)

  /*
   * Negative test.
   */

  li x2, 10
  la x3, _ed25519_ext_is_on_curve_x_neg
  bn.lid x2++, 0(x3)
  bn.lid x2++, 32(x3)

  jal x1, ext_is_on_curve

  bn.sel w0, w31, w1, FG0.Z
  la x3, _ed25519_ext_is_on_curve_res_neg
  bn.sid x0, 0(x3)

  ecall

.data
.balign 32

_ed25519_ext_is_on_curve_x_pos:
.zero 32
_ed25519_ext_is_on_curve_y_pos:
.zero 32

_ed25519_ext_is_on_curve_x_neg:
.zero 32
_ed25519_ext_is_on_curve_y_neg:
.zero 32

_ed25519_ext_is_on_curve_res_pos:
.zero 32
_ed25519_ext_is_on_curve_res_neg:
.zero 32
