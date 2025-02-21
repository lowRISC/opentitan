/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test to check an RSA keygen subroutine.
 *
 * The `relprime_small_primes` subroutine checks if a candidate prime is a
 * multiple of a small prime. This test ensures that the check detects a
 * multiple of 7.
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
 * A 1024-bit value that is a multiple of 7 and NOT 3, 5, 11, 17, or 31.
 *
 * Full value for reference =
 * 0x91986e138a0211deddc97f1f4284182b075166745a567a4866c7093a0e4ba084f82346b6572d6b3110ee488087c5b5385227e1671f48b4460afc72659e7e70521b347174161d184c63788c24b4b2e2db3fc1a6b56f86abfaeb7d19a2902a2223a2e51e15f5bc2b4a1f7ee67a1210881cb8b0c7a949efce5d4422e19865050a9f
 */
.balign 32
input:
.word 0x65050a9f
.word 0x4422e198
.word 0x49efce5d
.word 0xb8b0c7a9
.word 0x1210881c
.word 0x1f7ee67a
.word 0xf5bc2b4a
.word 0xa2e51e15
.word 0x902a2223
.word 0xeb7d19a2
.word 0x6f86abfa
.word 0x3fc1a6b5
.word 0xb4b2e2db
.word 0x63788c24
.word 0x161d184c
.word 0x1b347174
.word 0x9e7e7052
.word 0x0afc7265
.word 0x1f48b446
.word 0x5227e167
.word 0x87c5b538
.word 0x10ee4880
.word 0x572d6b31
.word 0xf82346b6
.word 0x0e4ba084
.word 0x66c7093a
.word 0x5a567a48
.word 0x07516674
.word 0x4284182b
.word 0xddc97f1f
.word 0x8a0211de
.word 0x91986e13
