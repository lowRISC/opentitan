/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Ensure that a good value for p passes RSA keygen checks.
 *
 * Uses the test data from `rsa_keygen_checkp_good_test.hjson`, which is sized
 * for RSA-2048.
 */

.section .text.start

main:
  /* Init all-zero register. */
  bn.xor    w31, w31, w31

  /* Load the number of limbs for this test. */
  li        x30, 4

  jal x1, fermat_test
  beq x2, x0, _end_test

  addi x3, x2, 0

  jal x1, miller_rabin_test
  and x2, x2, x3

_end_test:
  ecall
