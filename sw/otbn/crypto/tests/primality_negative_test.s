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

  /* Number of limbs (n) and related constant.
       x30 <= n
       x31 <= n - 1 */
  li        x30, 4
  li        x31, 3

  /* Compute Montgomery constants for the candidate prime.
       dmem[mont_m0inv] <= (- dmem[rsa_p]) mod 2^256
       dmem[mont_rr] <= (2^1024) mod dmem[input] */
  la         x16, rsa_p
  la         x18, mont_rr
  jal        x1, modload

  /* Load pointers to temporary work buffers. */
  la         x14, tmp0
  la         x15, tmp2

  /* Set number of Miller-Rabin rounds (see FIPS 186-5, table B.1). */
  li        x10, 4

  /* Call primality test.
       w21 <= all 1s if dmem[rsa_p] is probably prime, otherwise 0 */
  jal        x1, miller_rabin

  ecall

.data
