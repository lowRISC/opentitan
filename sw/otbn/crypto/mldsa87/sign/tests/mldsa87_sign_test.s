/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Top-level ML-DSA-87 sign test. */

.section .text.start

main:
  jal x0, mldsa87_sign
