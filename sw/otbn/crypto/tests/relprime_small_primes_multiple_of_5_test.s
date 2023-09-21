/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test to check an RSA keygen subroutine.
 *
 * The `relprime_small_primes` subroutine checks if a candidate prime is a
 * multiple of a small prime. This test ensures that the check detects a
 * multiple of 5.
 */

.section .text.start

main:
  /* Init all-zero register. */
  bn.xor    w31, w31, w31

  /* Load the number of limbs for this test. */
  li        x30, 4

  /* w22 <= 0 if dmem[simple_positive_input] is NOT relatively prime to F4 */
  la        x16, input
  jal       x1, relprime_small_primes

  ecall

.data

/**
 * A 1024-bit value that is a multiple of 5 and NOT 3, 7, 11, 17, or 31.
 *
 * Full value for reference =
 * 0x95746f2e1cadd653af519d764878e64c332cc27a5ccd76c989ff609bdee59d4d487c89bb09057b968afd2fd69fe76d25b99c1399a7b8e7e5f9bb301f6d62651a62c9c3aea5ff9e44f2f7065b96b16fda5b776f60760644686798018c960f96eaf2fa5e0dd0cbc707c4a06380dccaeea77ac0775afa2eb98d0e560c47f2ddb2bd
 */
.balign 32
input:
.word 0x2e6f7495
.word 0x53d6ad1c
.word 0x769d51af
.word 0x4ce67848
.word 0x7ac22c33
.word 0xc976cd5c
.word 0x9b60ff89
.word 0x4d9de5de
.word 0xbb897c48
.word 0x967b0509
.word 0xd62ffd8a
.word 0x256de79f
.word 0x99139cb9
.word 0xe5e7b8a7
.word 0x1f30bbf9
.word 0x1a65626d
.word 0xaec3c962
.word 0x449effa5
.word 0x5b06f7f2
.word 0xda6fb196
.word 0x606f775b
.word 0x68440676
.word 0x8c019867
.word 0xea960f96
.word 0x0d5efaf2
.word 0x07c7cbd0
.word 0x8063a0c4
.word 0xa7eecadc
.word 0x5a77c07a
.word 0x8db92efa
.word 0x470c560e
.word 0xbdb2ddf2
