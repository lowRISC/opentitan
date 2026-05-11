/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for X25519.
 *
 * Runs test vector 1 from RFC 7748, section 5.2:
 *   https://datatracker.ietf.org/doc/html/rfc7748#section-5.2
 */

.section .text.start

main:
  /* Prepare all-zero register and error counter */
  bn.xor  w31, w31, w31
  bn.mov  w0, w31

  /* w8 <= dmem[k] = enc(k) */
  li      x2, 8
  la      x3, k
  bn.lid  x2, 0(x3)

  /* w9 <= dmem[u] = enc(u) */
  li      x2, 9
  la      x3, u
  bn.lid  x2, 0(x3)

  /* Clamp the scalar in w8 */
  bn.rshi w8, w31, w8 >> 3
  bn.rshi w8, w8, w31 >> 251
  bn.addi w7, w31, 1
  bn.rshi w8, w7, w8 >> 2

  bn.mov  w2, w8
  bn.mov  w4, w31

  /* w22 <= X25519(k, u) */
  jal     x1, X25519

  /* w20 <= expected result */
  li      x2, 20
  la      x3, exp_result
  bn.lid  x2, 0(x3)

  /* Check result */
  jal     x1, check_result

  /* Check if there were any failures.
     If w0 != 0, fail the test deliberately. */
  bn.cmp  w0, w31
  csrrs   x2, FG0, x0
  andi    x2, x2, 8
  bne     x2, x0, test_pass

  /* Execute an illegal instruction to fail the simulation */
  unimp

test_pass:
  ecall

/**
 * Increment the error register if expected/actual results don't match.
 *
 * @param[in] w20: expected result
 * @param[in] w22: actual result (from X25519)
 * @param[in,out] w0: error count
 *
 * clobbered registers: w0, w1
 * clobbered flag groups: FG0
 */
check_result:
  bn.addi w1, w0, 1
  bn.cmp  w20, w22
  bn.sel  w0, w1, w0, C

  bn.addi w1, w0, 1
  bn.cmp  w22, w20
  bn.sel  w0, w1, w0, C
  ret

.data

.balign 32
k:
  .word 0x6be346a5
  .word 0x9d7c52f0
  .word 0x4b15163b
  .word 0xdd5e4682
  .word 0x0a4c1462
  .word 0x185afcc1
  .word 0x44226a50
  .word 0xc49a44ba

.balign 32
u:
  .word 0x6768dbe6
  .word 0xdb303058
  .word 0xa4c19435
  .word 0x7c5fb124
  .word 0xec246672
  .word 0x3b35b326
  .word 0xa603a910
  .word 0x4c1cabd0

.balign 32
exp_result:
  .word 0x3755dac3
  .word 0x90c6e99d
  .word 0x4dea948e
  .word 0x4f088df2
  .word 0x03cfec32
  .word 0xf7711c49
  .word 0x5507b454
  .word 0x5285a277
