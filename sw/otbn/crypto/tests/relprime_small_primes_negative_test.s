/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test to check an RSA keygen subroutine.
 *
 * The `relprime_small_primes` subroutine checks if a candidate prime is a
 * multiple of a small prime. This test ensures that the check does not think a
 * prime number is divisible by small primes.
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
 * A 1024-bit value that is prime.
 *
 * Full value for reference =
 * 0xde7d8c0eb2b3beca4db93f640590f62840bbe2435734ee154ef9dfd6eb5f8b9367a86989b88ee86dea529f5d1d62eb7fff904bd9a62d864a50aac31e5dec899a09255b18d8d61eca4b1bc038d3c655397cac166eb3ae6232e9dc11d31398fd4c0bb0af114cd5670c2c99f59cd6963500d0e9edcac0957b414a394ec915bd9377
 */
.balign 32
input:
.word 0x15bd9377
.word 0x4a394ec9
.word 0xc0957b41
.word 0xd0e9edca
.word 0xd6963500
.word 0x2c99f59c
.word 0x4cd5670c
.word 0x0bb0af11
.word 0x1398fd4c
.word 0xe9dc11d3
.word 0xb3ae6232
.word 0x7cac166e
.word 0xd3c65539
.word 0x4b1bc038
.word 0xd8d61eca
.word 0x09255b18
.word 0x5dec899a
.word 0x50aac31e
.word 0xa62d864a
.word 0xff904bd9
.word 0x1d62eb7f
.word 0xea529f5d
.word 0xb88ee86d
.word 0x67a86989
.word 0xeb5f8b93
.word 0x4ef9dfd6
.word 0x5734ee15
.word 0x40bbe243
.word 0x0590f628
.word 0x4db93f64
.word 0xb2b3beca
.word 0xde7d8c0e
