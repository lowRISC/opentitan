/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for Miller-Rabin primality test.
 *
 * The test input is composite, so we expect the primality test to fail. Uses
 * n=4 limbs (i.e. a 1024-bit prime candidate, as would be used in RSA-2048).
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
  jal        x1, miller_rabin_test

  ecall
