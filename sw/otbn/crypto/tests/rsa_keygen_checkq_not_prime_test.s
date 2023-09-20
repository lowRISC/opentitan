/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Ensure that a nonprime value for q fails RSA keygen checks.
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

  /* Copy a "good" p value into `rsa_p`. */
  la        x16, good_p
  la        x3, rsa_p
  loop      x30, 2
    bn.lid   x20, 0(x16++)
    bn.sid   x20, 0(x3++)

  /* Copy the nonprime value into `rsa_q`. */
  la        x16, not_prime
  la        x3, rsa_q
  loop      x30, 2
    bn.lid   x20, 0(x16++)
    bn.sid   x20, 0(x3++)

  /* w24 <= 2^256-1 if the check passed, otherwise 0 */
  jal       x1, check_q

  ecall
