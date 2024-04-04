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

/* Numerator: randomly-generated number in the range [0,2^256)
 = 0x87a0025a75bb55985e8122301cf43863578debae379c89e8f92af9a809f799bd */
.balign 32
numerator:
  .word 0x09f799bd
  .word 0xf92af9a8
  .word 0x379c89e8
  .word 0x578debae
  .word 0x1cf43863
  .word 0x5e812230
  .word 0x75bb5598
  .word 0x87a0025a

/*
Denominator: randomly-generated number in the range [0,2^128)
= 0x775c2b87508ba83e45403b541eb3edb4
*/
.balign 32
denominator:
  .word 0x1eb3edb4
  .word 0x45403b54
  .word 0x508ba83e
  .word 0x775c2b87
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000

/* Buffer for quotient. */
.balign 32
quotient:
.zero 32
