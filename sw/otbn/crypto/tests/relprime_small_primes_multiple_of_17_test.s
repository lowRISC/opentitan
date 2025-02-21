/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test to check an RSA keygen subroutine.
 *
 * The `relprime_small_primes` subroutine checks if a candidate prime is a
 * multiple of a small prime. This test ensures that the check detects a
 * multiple of 17.
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
 * A 1024-bit value that is a multiple of 17 and NOT 3, 5, 11, 17, or 31.
 *
 * Full value for reference =
 * 0x5143649b8bf054404d0ebedfa7a956dabd297218a15c6410335f8fc10f679ea7b4c0c055a34801e48f9a22cc124580ae9de9fda12300eb6cc6a5ab1e9edb8ff24329ef86ec8833131fbfcbbf8e97f9ac5475dc577367b017cb30d1df1c4baa3c63be79499d79f3e1fda86b6ad1790701b6156e77604ad67d9a8e49e8a4c2a845
 */
.balign 32
input:
.word 0xa4c2a845
.word 0x9a8e49e8
.word 0x604ad67d
.word 0xb6156e77
.word 0xd1790701
.word 0xfda86b6a
.word 0x9d79f3e1
.word 0x63be7949
.word 0x1c4baa3c
.word 0xcb30d1df
.word 0x7367b017
.word 0x5475dc57
.word 0x8e97f9ac
.word 0x1fbfcbbf
.word 0xec883313
.word 0x4329ef86
.word 0x9edb8ff2
.word 0xc6a5ab1e
.word 0x2300eb6c
.word 0x9de9fda1
.word 0x124580ae
.word 0x8f9a22cc
.word 0xa34801e4
.word 0xb4c0c055
.word 0x0f679ea7
.word 0x335f8fc1
.word 0xa15c6410
.word 0xbd297218
.word 0xa7a956da
.word 0x4d0ebedf
.word 0x8bf05440
.word 0x5143649b
