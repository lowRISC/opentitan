/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test to check an RSA keygen subroutine.
 *
 * The `relprime_small_primes` subroutine checks if a candidate prime is a
 * multiple of a small prime. This test ensures that the check detects a
 * multiple of 31.
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
 * A 1024-bit value that is a multiple of 31 and NOT 3, 5, 7, 11, or 17.
 *
 * Full value for reference =
 * 0xc6b202813cf17e3c55fefc6282020980fa205b3ccfb384f597e2c0749b1d5213c2ebbf45d5f239e911062650cd43d3c008183c6c2cf217ac48af2bcfeac39a280afd60eea8508324e97f40fa78d5d70a5b5fcb80c1e260feaa1f02f54c072a915d48a0d13a162f1e22f40b26c1eb29d4e7a44c48956c2daa5edfd222e7cf7221
 */
.balign 32
input:
.word 0xe7cf7221
.word 0x5edfd222
.word 0x956c2daa
.word 0xe7a44c48
.word 0xc1eb29d4
.word 0x22f40b26
.word 0x3a162f1e
.word 0x5d48a0d1
.word 0x4c072a91
.word 0xaa1f02f5
.word 0xc1e260fe
.word 0x5b5fcb80
.word 0x78d5d70a
.word 0xe97f40fa
.word 0xa8508324
.word 0x0afd60ee
.word 0xeac39a28
.word 0x48af2bcf
.word 0x2cf217ac
.word 0x08183c6c
.word 0xcd43d3c0
.word 0x11062650
.word 0xd5f239e9
.word 0xc2ebbf45
.word 0x9b1d5213
.word 0x97e2c074
.word 0xcfb384f5
.word 0xfa205b3c
.word 0x82020980
.word 0x55fefc62
.word 0x3cf17e3c
.word 0xc6b20281
