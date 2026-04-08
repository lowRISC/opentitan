/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Test we can correctly invert a element modulo L. */

.section .text.start

main:
  bn.xor w31, w31, w31

  jal x1, sc_init

  /* [w1, w0] <= x. */
  li x2, 23
  la x3, _sc_mod_inv_x
  bn.lid x2, 0(x3)

  jal x1, sc_mod_inv

  ecall

.data
.balign 32

_sc_mod_inv_x:
.zero 32
_sc_mod_inv_y:
.zero 32
