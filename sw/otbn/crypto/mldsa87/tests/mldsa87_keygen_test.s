/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Top-level ML-DSA-87 keygen test. */

.section .text.start

main:
  jal x1, mldsa87_keygen

  /*
   * Unmask shared values.
   */

  la x20, mldsa87_sk_k_share0
  la x21, mldsa87_sk_k_share1
  li x22, 1
  jal x1, unmask_boolean

  la x20, mldsa87_sk_s1_share0
  la x21, mldsa87_sk_s1_share1
  li x22, 21
  jal x1, unmask_boolean

  la x20, mldsa87_sk_s2_share0
  la x21, mldsa87_sk_s2_share1
  li x22, 24
  jal x1, unmask_boolean

  ecall
