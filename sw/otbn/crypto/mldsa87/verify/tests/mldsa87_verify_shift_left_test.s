/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Test that a polynomial can be correctly multiplied (left-shifted) by 2^13. */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x2, _shift_left_x
  la x3, _shift_left_y
  jal x1, shift_left

  ecall

.data
.balign 32

_shift_left_x:
.zero 1024
_shift_left_y:
.zero 1024

_stack:
.zero 4
