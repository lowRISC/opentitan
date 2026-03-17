/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x2, _decode_h_h_enc
  la x3, _decode_h_h0
  addi x4, x0, 0

  /* Decode all 8 hint polynomials. */
  loopi 8, 3
    jal x1, decode_h
    addi x3, x3, 1024
    addi x4, x4, 1
    /* End of loop */

  ecall

.data
.balign 32

_decode_h_h_enc:
.zero 336
.zero 16 /* Padding */

_decode_h_h0:
.zero 1024
_decode_h_h1:
.zero 1024
_decode_h_h2:
.zero 1024
_decode_h_h3:
.zero 1024
_decode_h_h4:
.zero 1024
_decode_h_h5:
.zero 1024
_decode_h_h6:
.zero 1024
_decode_h_h7:
.zero 1024

_stack:
.zero 4
