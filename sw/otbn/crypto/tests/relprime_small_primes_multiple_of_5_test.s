/* Copyright lowRISC contributors. */
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
 * A 1024-bit value that is a multiple of 5 and NOT 3 or 17.
 *
 * Full value for reference =
 * 0x7dd35aeb866062ae017ae1f605b19b348668ad55367975302fa84bc99ef347339199cdb22e9bd1f4ef3340edc27e18b79ad3168f7bba3f36bd642650d1e0fc061f17fe99ba598320a03b3f503e63d9017b375642188965eda30f5d792390a6cc080768f3e1d07e76b992e92a1f7f383bb40ef314e55b90ec12e4323a97af0ac5
 */
.balign 32
input:
.word 0x97af0ac5
.word 0x12e4323a
.word 0xe55b90ec
.word 0xb40ef314
.word 0x1f7f383b
.word 0xb992e92a
.word 0xe1d07e76
.word 0x080768f3
.word 0x2390a6cc
.word 0xa30f5d79
.word 0x188965ed
.word 0x7b375642
.word 0x3e63d901
.word 0xa03b3f50
.word 0xba598320
.word 0x1f17fe99
.word 0xd1e0fc06
.word 0xbd642650
.word 0x7bba3f36
.word 0x9ad3168f
.word 0xc27e18b7
.word 0xef3340ed
.word 0x2e9bd1f4
.word 0x9199cdb2
.word 0x9ef34733
.word 0x2fa84bc9
.word 0x36797530
.word 0x8668ad55
.word 0x05b19b34
.word 0x017ae1f6
.word 0x866062ae
.word 0x7dd35aeb
