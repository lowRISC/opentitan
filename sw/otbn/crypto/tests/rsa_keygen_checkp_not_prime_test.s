/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Ensure that a nonprime value for p fails RSA keygen checks.
 *
 * Uses the test data from `rsa_keygen_checkpq_test_data`, which is sized for
 * RSA-2048.
 */

.section .text.start

main:
  /* Init all-zero register. */
  bn.xor    w31, w31, w31

  /* Load the number of limbs for this test. */
  li        x30, 4
  li        x31, 3

  /* Load required constants. */
  li        x20, 20
  li        x21, 21

  /* Check a value of p that is nonprime.
       w24 <= 2^256-1 if the check passed, otherwise 0 */
  la        x16, not_prime
  jal       x1, check_p

  ecall
