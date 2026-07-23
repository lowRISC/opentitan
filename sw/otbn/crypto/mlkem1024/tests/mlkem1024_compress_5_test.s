/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  /* Set MOD CSR with Q = 3329 */
  la x2, _params
  bn.lid x0, 0(x2)
  bn.wsrw 0, w0

  la x2, _poly_in
  la x3, _bytes_out
  jal x1, compress_5

  ecall

.data
.balign 32

_params:
.word 3329, 0x94570CFF, 0, 0, 0, 0, 0, 0

_poly_in:
.zero 1024

_bytes_out:
.zero 160
