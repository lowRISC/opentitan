/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x2, _bytes_in
  la x3, _poly_out
  jal x1, decode_1

  ecall

.data
.balign 32

_bytes_in:
.zero 32

_poly_out:
.zero 1024
