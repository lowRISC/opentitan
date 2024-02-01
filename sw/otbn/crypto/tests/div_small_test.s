/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for OTBN bignum division.
 */

.section .text.start

main:
  /* Init all-zero register. */
  bn.xor    w31, w31, w31

  /* Load the number of limbs for this test. */
  li        x30, 1

  /* Load DMEM pointers. */
  la        x10, numerator
  la        x11, denominator
  la        x12, quotient

  /* Compute the result.
       dmem[quotient] <= dmem[numerator] // dmem[denominator]
       dmem[remainder] <= dmem[numerator] % dmem[denominator] */
  jal       x1, div

  /* Read the quotient and remainder into registers for the test framework to
     check.
       w0 <= dmem[quotient] = quotient
       w1 <= dmem[numerator] = remainder */
  li        x2, 0
  bn.lid    x2++, 0(x12)
  bn.lid    x2, 0(x10)

  ecall

.data

/* Numerator: 407 = 0x197 */
.balign 32
numerator:
.word 0x00000197
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000

/* Denominator: 27 = 0x1b */
.balign 32
denominator:
.word 0x0000001b
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000

/* Buffer for quotient. */
.balign 32
quotient:
.zero 32
