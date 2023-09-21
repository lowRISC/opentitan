/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test to check an RSA keygen subroutine.
 *
 * The `relprime_small_primes` subroutine checks if a candidate prime is a
 * multiple of a small prime. This test ensures that the check detects a
 * multiple of 11.
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
 * A 1024-bit value that is a multiple of 11 and NOT 3, 5, 7, 17, or 31.
 *
 * Full value for reference =
 */
.balign 32
input:
.word 0x0a9a411f
.word 0xca52e7f3
.word 0x2c301918
.word 0x948c97b0
.word 0x171f68fc
.word 0xe36be04a
.word 0x0a7ffbaa
.word 0xf9cf072d
.word 0x51b76bd5
.word 0x19d0fec0
.word 0x0771be64
.word 0x49c95131
.word 0x1ed7cd7a
.word 0xda4a6077
.word 0x11fa0022
.word 0x66e409f1
.word 0x95548bfd
.word 0x7938113a
.word 0x9296d0f5
.word 0x1352294c
.word 0x33eaf657
.word 0x6c47a7dc
.word 0xf57e2b6b
.word 0xd1194a3e
.word 0x84402e7e
.word 0x87641b66
.word 0x2c3c225e
.word 0x5e27e299
.word 0x5ee52414
.word 0xab6816c2
.word 0x0ea3266c
.word 0x5f4b97ff
