/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone tests for X25519.
 *
 * This test will exit with the number of failures written to the w0 register;
 * w0=0 means all tests succeeded.
 */

.section .text.start

main:
  /* Initialize failure counter to 0.
       w0 <= 0 */
  bn.xor  w0, w0, w0

  /* Run tests. */
  jal  x1, run_test1
  jal  x1, run_test2

  ecall

run_test1:
  /* w8 <= dmem[test1_k] = enc(k) */
  li      x2, 8
  la      x3, test1_k
  bn.lid  x2, 0(x3)

  /* w9 <= dmem[test1_u] = enc(u) */
  li      x2, 9
  la      x3, test1_u
  bn.lid  x2, 0(x3)

  /* w22 <= X25519(k, u) */
  jal     x1, X25519

  /* w25 <= dmem[test1_exp_result] */
  li      x2, 25
  la      x3, test1_exp_result
  bn.lid  x2, 0(x3)

  jal     x1, check_result

  ret

run_test2:
  /* w8 <= dmem[test2_k] = enc(k) */
  li      x2, 8
  la      x3, test2_k
  bn.lid  x2, 0(x3)

  /* w9 <= dmem[test2_u] = enc(u) */
  li      x2, 9
  la      x3, test2_u
  bn.lid  x2, 0(x3)

  /* w22 <= X25519(k, u) */
  jal     x1, X25519

  /* w25 <= dmem[test2_exp_result] */
  li      x2, 25
  la      x3, test2_exp_result
  bn.lid  x2, 0(x3)

  jal     x1, check_result

  ret

/**
 * Increment the failure counter if expected/actual results don't match.
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

/* Test vector 1 from RFC 7748, section 5.2:
     https://datatracker.ietf.org/doc/html/rfc7748#section-5.2 */

.balign 32
test1_k:
  .word 0x6be346a5
  .word 0x9d7c52f0
  .word 0x4b15163b
  .word 0xdd5e4682
  .word 0x0a4c1462
  .word 0x185afcc1
  .word 0x44226a50
  .word 0xc49a44ba

.balign 32
test1_u:
  .word 0x6768dbe6
  .word 0xdb303058
  .word 0xa4c19435
  .word 0x7c5fb124
  .word 0xec246672
  .word 0x3b35b326
  .word 0xa603a910
  .word 0x4c1cabd0

.balign 32
test1_exp_result:
  .word 0x3755dac3
  .word 0x90c6e99d
  .word 0x4dea948e
  .word 0x4f088df2
  .word 0x03cfec32
  .word 0xf7711c49
  .word 0x5507b454
  .word 0x5285a277


/* Test vector 2 from RFC 7748, section 5.2:
     https://datatracker.ietf.org/doc/html/rfc7748#section-5.2 */

.balign 32
test2_k:
  .word 0xd4e9664b
  .word 0x3c67b4d1
  .word 0x9126d25a
  .word 0xf56a7d95
  .word 0x21641bc1
  .word 0xd401eae0
  .word 0x9e16a42c
  .word 0x0dba1879

.balign 32
test2_u:
  .word 0x120f21e5
  .word 0xd3116878
  .word 0x9d95b7f4
  .word 0x2cae3805
  .word 0x10e7db31
  .word 0x3e3cc06f
  .word 0x49d54cfc
  .word 0x93a415c7

.balign 32
test2_exp_result:
  .word 0x94decb95
  .word 0x7d90e876
  .word 0x5ce4ad7a
  .word 0xf873b8b4
  .word 0x685a598b
  .word 0x52a19f79
  .word 0x64f7f8e6
  .word 0x5779ac7a
