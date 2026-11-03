/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for the RSA modulus check (composite and not a prime power).
 *
 * Runs `rsa_check_modulus` on a 2048-bit modulus (n=8 limbs). The expected
 * hardened boolean result in x2 is given by the testcase.
 */

.section .text.start

main:
  /* Initialize all-zero register. */
  bn.xor    w31, w31, w31

  /* Number of limbs (n).
       x30 <= n */
  li        x30, 8

  /* Check the modulus.
       x2 <= HARDENED_BOOL_TRUE if dmem[rsa_n] is composite and not a prime
             power, otherwise HARDENED_BOOL_FALSE */
  jal       x1, rsa_check_modulus

  ecall
