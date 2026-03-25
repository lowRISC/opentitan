/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Top-level ML-DSA-87 verify test. */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x2, mldsa87_verify_const_params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  jal x1, mldsa87_verify

  ecall
