/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Test that e^-1 mod lambda(p - 1, q - 1) is computed correctly. */

.section .text.start

main:
  bn.xor w31, w31, w31

  la x24, _modinv_f4_lambda
  la x25, _modinv_f4_einv
  la x26, _modinv_f4_tmp
  addi x27, x30, 0
  jal x1, modinv_f4

  ecall

.data
.balign 32

_modinv_f4_lambda:
.zero 512
_modinv_f4_einv:
.zero 512
.zero 32
_modinv_f4_tmp:
.zero 512
