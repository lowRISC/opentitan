/* Copyright lowRISC contributors (OpenTitan project). */
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
 * A 1024-bit value that is a multiple of 3 and NOT 5, 7, 11, 17, or 31.
 *
 * Full value for reference =
 * 0xaf8f432e511b6294ef296e4c0c73fdad210a09a5355a5150cc190b64f9e384fbc3bff603b12bf716d6b7493876ea0aa119eb3cca8706f1cfde452289edf554350bfec6b4812f05bcfd3d799c703a901cf7bc99536b6d1c0df187a62eed3114384bba11b8132de7aed844a98ac7597ea336a01df3664d9ebf3126dc99a5896a45
 */
.balign 32
input:
.word 0xa5896a45
.word 0x3126dc99
.word 0x664d9ebf
.word 0x36a01df3
.word 0xc7597ea3
.word 0xd844a98a
.word 0x132de7ae
.word 0x4bba11b8
.word 0xed311438
.word 0xf187a62e
.word 0x6b6d1c0d
.word 0xf7bc9953
.word 0x703a901c
.word 0xfd3d799c
.word 0x812f05bc
.word 0x0bfec6b4
.word 0xedf55435
.word 0xde452289
.word 0x8706f1cf
.word 0x19eb3cca
.word 0x76ea0aa1
.word 0xd6b74938
.word 0xb12bf716
.word 0xc3bff603
.word 0xf9e384fb
.word 0xcc190b64
.word 0x355a5150
.word 0x210a09a5
.word 0x0c73fdad
.word 0xef296e4c
.word 0x511b6294
.word 0xaf8f432e
