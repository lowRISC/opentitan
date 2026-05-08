/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Test that x mod 2^16 + 1 is computed correctly. */

.section .text.start

main:
  bn.xor w31, w31, w31

  la x16, _mod_f4_x_coprime
  addi x21, x31, 0
  jal x1, mod_f4

  la x16, _mod_f4_y_coprime
  bn.mov w0, w22
  bn.sid x0, 0(x16)

  la x16, _mod_f4_x_multiple
  addi x21, x31, 0
  jal x1, mod_f4

  la x16, _mod_f4_y_multiple
  bn.mov w0, w22
  bn.sid x0, 0(x16)

  ecall

.data
.balign 32

_mod_f4_x_coprime:
.zero 512
_mod_f4_x_multiple:
.zero 512

_mod_f4_y_coprime:
.zero 32
_mod_f4_y_multiple:
.zero 32
