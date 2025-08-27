/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for Miller-Rabin primality test.
 *
 * The prime candidate in this case is a true prime, so we expect the primality
 * test to succeed. Uses n=2 limbs (i.e. a 512-bit prime candidate, as would be
 * used in RSA-1024).
 */

.section .text.start

main:
  /* Initialize all-zero register. */
  bn.xor    w31, w31, w31

  /* Number of limbs (n) and related constant.
       x30 <= n
       x31 <= n - 1 */
  li        x30, 2
  li        x31, 1

  /* Compute Montgomery constants for the candidate prime.
       dmem[mont_m0inv] <= (- dmem[rsa_p]) mod 2^256
       dmem[mont_rr] <= (2^1024) mod dmem[rsa_p] */
  la         x16, rsa_p
  la         x17, mont_m0inv
  la         x18, mont_rr
  jal        x1, modload


  /* Load pointers to temporary work buffers. */
  la         x14, tmp0
  la         x15, tmp1

  /* Set number of Miller-Rabin rounds. The prime should survive any number of
     rounds, but we set a roughly realistic number. */
  li        x10, 4

  /* Call primality test.
       w21 <= all 1s if dmem[rsa_p] is probably prime, otherwise 0 */
  jal        x1, miller_rabin

  /* Load Mont constants.
       w0 <= m0_inv
       w1, w2 <= rr */
  la         x17, mont_m0inv
  la         x18, mont_rr
  li         x2, 0
  bn.lid     x2++, 0(x17)
  bn.lid     x2++, 0(x18)
  bn.lid     x2++, 32(x18)

  ecall
