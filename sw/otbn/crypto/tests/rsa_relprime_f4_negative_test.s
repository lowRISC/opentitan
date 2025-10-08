/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Ensure that a multiple of F4 fails RSA keygen checks for p.
 */

.section .text.start

main:
  /* Init all-zero register. */
  bn.xor    w31, w31, w31

  /* Load the number of limbs for this test. */
  li        x30, 4

  /* Check a value of p that is not relatively prime to F4.
       w24 <= 2^256-1 if the check passed, otherwise 0 */
  la        x16, rsa_n
  jal       x1, relprime_f4_test

  ecall
