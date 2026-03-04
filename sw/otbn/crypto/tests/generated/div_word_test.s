/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Test that we can correctly divide a multi-limbed int by a single-word integer. */

.section .text.start

main:
  bn.xor w31, w31, w31

  la x16, _div_x
  jal x1, div_word

  ecall

.data
.balign 32

_div_x:
.zero 512
