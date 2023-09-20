/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test to check an RSA keygen subroutine.
 *
 * The `relprime_small_primes` subroutine checks if a candidate prime is a
 * multiple of a small prime. This test ensures that the check detects a
 * multiple of 3.
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
 * A 1024-bit value that is a multiple of 3 and NOT 5 or 17.
 *
 * Full value for reference =
 * 0x859619e48009dbf121db2000c823862f3ac30d8806a7babf54e784b3a8e2a63c70cca37ce01839e3c6eb780ce56eed882cb9603835f194b2f93ec68a397229d0159827ceb0881ef9c54bc11956b19b9894b2f99373d4d7996bf59a4bcb592cc0933519023a53e46b311acf7565307ad9a419d45066edbfb174bbb8169d56b246
 */
.balign 32
input:
.word 0x9d56b246
.word 0x74bbb816
.word 0x66edbfb1
.word 0xa419d450
.word 0x65307ad9
.word 0x311acf75
.word 0x3a53e46b
.word 0x93351902
.word 0xcb592cc0
.word 0x6bf59a4b
.word 0x73d4d799
.word 0x94b2f993
.word 0x56b19b98
.word 0xc54bc119
.word 0xb0881ef9
.word 0x159827ce
.word 0x397229d0
.word 0xf93ec68a
.word 0x35f194b2
.word 0x2cb96038
.word 0xe56eed88
.word 0xc6eb780c
.word 0xe01839e3
.word 0x70cca37c
.word 0xa8e2a63c
.word 0x54e784b3
.word 0x06a7babf
.word 0x3ac30d88
.word 0xc823862f
.word 0x21db2000
.word 0x8009dbf1
.word 0x859619e4
