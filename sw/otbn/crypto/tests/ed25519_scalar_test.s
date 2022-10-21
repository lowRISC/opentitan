/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for Ed25519 scalar field arithmetic.
 *
 * This test will exit with the number of failures written to the w0 register;
 * w0=0 means all tests succeeded.
 */

.section .text.start

main:
  /* Prepare all-zero register. */
  bn.xor w31, w31, w31

  /* Initialize failure counter to 0. */
  bn.mov w0, w31

  /* Initialize scalar field constants.
       MOD <= L (Ed25519 curve order)
       [w15:w14] <= mu (precomputed constant) */
  jal    x1, sc_init

  /* Call reduce test. */
  jal    x1, sc_reduce_test

  /* Call multiply test. */
  jal    x1, sc_mul_test

  ecall

sc_reduce_test:
  /* w16 <= (-1) mod 2^256 = 2^256 - 1 */
  bn.subi w16, w31, 1

  /* [w17:w16] <= 2^512 - 1 */
  bn.mov  w17, w16

  /* w18 <= sc_reduce(2^512 - 1) */
  jal     x1, sc_reduce

  /* w20 <= expected result = (2^512 - 1) mod L */
  li      x2, 20
  la      x3, sc_reduce_test_exp
  bn.lid  x2, 0(x3)

  /* w0 <= (w18 == w20) ? w0 : w0 + 1 */
  jal     x1, check_result

  ret

sc_mul_test:
  /* w21 <= dmem[sc_mul_test_lhs] */
  li      x2, 21
  la      x3, sc_mul_test_lhs
  bn.lid  x2++, 0(x3)

  /* w22 <= dmem[sc_mul_test_rhs] */
  la      x3, sc_mul_test_rhs
  bn.lid  x2, 0(x3)

  /* w18 <= sc_mul(w20, w21) */
  jal     x1, sc_mul

  /* w20 <= dmem[sc_mul_test_exp] */
  li      x2, 20
  la      x3, sc_mul_test_exp
  bn.lid  x2, 0(x3)

  /* w0 <= (w18 == w20) ? w0 : w0 + 1 */
  jal     x1, check_result

  ret

/**
 * Increment the error register if expected/actual results don't match.
 *
 * @param[in] w20: expected result
 * @param[in] w18: actual result
 * @param[in,out] w0: error count
 *
 * clobbered registers: w0, w1
 * clobbered flag groups: FG0
 */
check_result:
  /* Increment error register if expected < actual. */
  bn.addi w1, w0, 1
  bn.cmp  w20, w18
  bn.sel  w0, w1, w0, C

  /* Increment error register if actual < expected. */
  bn.addi w1, w0, 1
  bn.cmp  w18, w20
  bn.sel  w0, w1, w0, C

  ret

.data

/* Expected result for sc_reduce_test: (2^512 - 1) mod L */
.balign 32
sc_reduce_test_exp:
  .word 0x449c0f00
  .word 0xa40611e3
  .word 0x68859347
  .word 0xd00e1ba7
  .word 0x17f5be65
  .word 0xceec73d2
  .word 0x7c309a3d
  .word 0x0399411b


/* Randomly-generated input for sc_mul_test. */
.balign 32
sc_mul_test_lhs:
  .word 0x096d043c
  .word 0x97982132
  .word 0x4404e505
  .word 0xe67fef52
  .word 0x6e811e76
  .word 0xdb84b492
  .word 0x73b00211
  .word 0x4452ec61

/* Randomly-generated input for sc_mul_test. */
.balign 32
sc_mul_test_rhs:
  .word 0x5493c1eb
  .word 0xde89e6d6
  .word 0xb65a4b20
  .word 0xdb077dfc
  .word 0x2f3f3a0c
  .word 0xd224a8b7
  .word 0xfd8527c7
  .word 0xfb30c823

/* Expected result for sc_mul_test. */
.balign 32
sc_mul_test_exp:
  .word 0xa1f69e48
  .word 0x51fa0d05
  .word 0x1032b6b5
  .word 0x422d3a89
  .word 0xd773a1f5
  .word 0x8e41e298
  .word 0xb6aef1f8
  .word 0x0c737a37
