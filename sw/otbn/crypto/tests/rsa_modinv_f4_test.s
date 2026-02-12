/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Test for an RSA keygen subroutine: modular inverse of F4.
 */

.section .text.start

main:
  /* Init all-zero register. */
  bn.xor    w31, w31, w31

  /* Load the number of limbs for this test. */
  li        x30, 4

  /* Load DMEM pointers. */
  la        x12, rsa_n
  la        x13, rsa_d0
  la        x14, r1
  la        x15, r2

  /* Load required constants. */
  li        x20, 20
  li        x21, 21

  /* Compute the modular inverse.
       dmem[result] <= (65537^-1) mod dmem[modulus] */
  jal       x1, modinv_f4

  /* Read the inverse into registers for the test framework to check.
       [w0..w3] <= dmem[result] */
  li        x2, 0
  loop      x30, 2
    bn.lid    x2, 0(x13++)
    addi      x2, x2, 1

  ecall
