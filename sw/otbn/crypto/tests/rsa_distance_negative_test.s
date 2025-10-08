/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Ensure that a value for q which is too close to p fails RSA keygen checks.
 *
 * Uses the test data from `rsa_distance_negative_test`, which is sized
 * for RSA-2048.
 */

.section .text.start

main:
  /* Initialize all-zero register. */
  bn.xor    w31, w31, w31

  /* Number of limbs (n).
       x30 <= n */
  li        x30, 4

  /* Call primality test.
       x2 <= 1 if dmem[n] is probably prime, otherwise 0 */
  jal        x1, distance_test

  ecall
