/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Top-level ML-DSA-87 verify test. */

.section .text.start

main:
  jal x1, mldsa87_verify

  ecall
