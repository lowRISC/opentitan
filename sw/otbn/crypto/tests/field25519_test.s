/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for X25519/Ed25519 finite field arithmetic routines.
 *
 * This test will exit with the number of failures written to the w0 register;
 * w0=0 means all tests succeeded.
 */

.section .text.start

main:
  /* Prepare all-zero register. */
  bn.xor w31, w31, w31

  /* MOD <= dmem[modulus] = p */
  li      x2, 2
  la      x3, modulus
  bn.lid  x2, 0(x3)
  bn.wsrw MOD, w2

  /* w19 <= 19 */
  bn.addi w19, w31, 19

  /* Call multiply test. */
  jal     x1, fe_mul_test

  /* Call square test. */
  jal     x1, fe_square_test

  /* Call inverse test. */
  jal     x1, fe_inv_test

  ecall

fe_mul_test:
  /* w22 <= dmem[value_x] = x */
  li      x2, 22
  la      x3, value_x
  bn.lid  x2++, 0(x3)

  /* w23 <= dmem[value_y] = y */
  la      x3, value_y
  bn.lid  x2, 0(x3)

  /* w22 <= femul(w22, w23) = (x * y) mod p */
  jal     x1, fe_mul

  /* Since x = 1, we expect (x * y) mod p == y. */
  bn.mov  w25, w23
  jal     x1, check_result

  ret

fe_square_test:
  /* w22 <= dmem[value_y] = y */
  li      x2, 22
  la      x3, value_y
  bn.lid  x2, 0(x3)

  /* w22 <= fe_square(w22) = (y^2) mod p */
  jal     x1, fe_square

  /* Since y = p-2, we expect (y^2) mod p == 4. */
  bn.addi w25, w31, 4
  jal     x1, check_result

  ret

fe_inv_test:
  /* w16 <= dmem[value_y] = y */
  li      x2, 16
  la      x3, value_y
  bn.lid  x2, 0(x3)

  /* w2 <= w16 = y */
  bn.mov  w2, w16

  /* w22 <= fe_inv(w16) = (y^-1) mod p */
  jal     x1, fe_inv

  /* w22 <= fe_mul(w22, w23) = (y * y^-1) mod p */
  bn.mov  w23, w2
  jal     x1, fe_mul

  /* Check that (y * y^-1) mod p is 1. */
  bn.addi w25, w31, 1
  jal     x1, check_result

  ret

/**
 * Increment the error register if expected/actual results don't match.
 *
 * @param[in] w25: expected result
 * @param[in] w22: actual result
 * @param[in,out] w0: error count
 *
 * clobbered registers: w0, w1
 * clobbered flag groups: FG0
 */
check_result:
  /* Increment error register if expected < actual. */
  bn.addi w1, w0, 1
  bn.cmp  w22, w25
  bn.sel  w0, w1, w0, C

  /* Increment error register if actual < expected. */
  bn.addi w1, w0, 1
  bn.cmp  w25, w22
  bn.sel  w0, w1, w0, C
  ret

.data

/* Modulus p = 2^255 - 19. */
.balign 32
modulus:
  .word 0xffffffed
  .word 0xffffffff
  .word 0xffffffff
  .word 0xffffffff
  .word 0xffffffff
  .word 0xffffffff
  .word 0xffffffff
  .word 0x7fffffff

/* Test input value x = 1. */
.balign 32
value_x:
  .word 0x00000001
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000

/* Test input value y = p - 2. */
.balign 32
value_y:
  .word 0xffffffeb
  .word 0xffffffff
  .word 0xffffffff
  .word 0xffffffff
  .word 0xffffffff
  .word 0xffffffff
  .word 0xffffffff
  .word 0x7fffffff
