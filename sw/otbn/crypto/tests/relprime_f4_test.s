/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test to check an RSA keygen subroutine.
 *
 * In RSA key generation, GCD(p,e) must be 1 for a potential prime p and an
 * exponent e. When e is fixed to 65537 (aka F4), we use a specialized routine
 * to ensure the GCD is 1.
 */

.section .text.start

main:
  /* Init all-zero register. */
  bn.xor    w31, w31, w31

  /* w0 <= 0 if simple_positive_test succeeded, 2^256-1 if it failed. */
  jal       x1, simple_positive_test
  /* w1 <= 0 if simple_negative_test succeeded, 2^256-1 if it failed. */
  jal       x1, simple_negative_test
  /* w2 <= 0 if edge_case_test succeeded, 2^256-1 if it failed. */
  jal       x1, edge_case_test

  ecall

simple_positive_test:
  /* Load the number of limbs for this test. */
  li        x30, 4

  /* w22 <= 0 if dmem[simple_positive_input] is NOT relatively prime to F4 */
  la        x16, simple_positive_input
  jal       x1, relprime_f4

  /* w23 <= ~w31 = 2^256-1 (failure value) */
  bn.not    w23, w31

  /* FG0.Z <= (w22 == 0) */
  bn.add    w22, w22, w31

  /* We expect a nonzero value in w22, since the input is relatively prime.
      w0 <= (w22 == 0) ? 2^256-1 (failure) : 0 (success) */
  bn.sel    w0, w23, w31, FG0.Z

  ret

simple_negative_test:
  /* Load the number of limbs for this test. */
  li        x30, 4

  /* w22 <= 0 if dmem[simple_positive_input] is NOT relatively prime to F4 */
  la        x16, simple_negative_input
  jal       x1, relprime_f4

  /* w23 <= ~w31 = 2^256-1 (failure value) */
  bn.not    w23, w31

  /* FG0.Z <= (w22 == 0) */
  bn.add    w22, w22, w31

  /* We expect a zero value in w22, since the input is NOT relatively prime.
      w1 <= (w22 == 0) ? 0 (success) : 2^256-1 (failure) */
  bn.sel    w1, w31, w23, FG0.Z

  ret

edge_case_test:
  /* Load the number of limbs for this test. */
  li        x30, 4

  /* w22 <= 0 if dmem[edge_case_input] is NOT relatively prime to F4 */
  la        x16, edge_case_input
  jal       x1, relprime_f4

  /* w23 <= ~w31 = 2^256-1 (failure value) */
  bn.not    w23, w31

  /* FG0.Z <= (w22 == 0) */
  bn.add    w22, w22, w31

  /* We expect a nonzero value in w22, since the input is relatively prime.
      w2 <= (w22 == 0) ? 2^256-1 (failure) : 0 (success) */
  bn.sel    w2, w23, w31, FG0.Z

  ret

.data

/**
 * A 1024-bit value that *is* relatively prime to F4.
 *
 * Full value for reference =
 * 0xf473d9ff366276da71a73afbf03ff01f8ec9148a71798d74dc6f44d961bef880927cc05f07243ce92f5350972532b38bf63efbb65a272de2e9faa34f3bb3520b25e2269c231eb09b0a2b5cb604cfc7e016a2f1a20be61ac1251e0b34b589bb08d1d4542c39ef080b96e60aebb6a37039c84c5591d288465d47e7bc30bf36fc34
 */
.balign 32
simple_positive_input:
  .word 0xbf36fc34
  .word 0x47e7bc30
  .word 0xd288465d
  .word 0xc84c5591
  .word 0xb6a37039
  .word 0x96e60aeb
  .word 0x39ef080b
  .word 0xd1d4542c
  .word 0xb589bb08
  .word 0x251e0b34
  .word 0x0be61ac1
  .word 0x16a2f1a2
  .word 0x04cfc7e0
  .word 0x0a2b5cb6
  .word 0x231eb09b
  .word 0x25e2269c
  .word 0x3bb3520b
  .word 0xe9faa34f
  .word 0x5a272de2
  .word 0xf63efbb6
  .word 0x2532b38b
  .word 0x2f535097
  .word 0x07243ce9
  .word 0x927cc05f
  .word 0x61bef880
  .word 0xdc6f44d9
  .word 0x71798d74
  .word 0x8ec9148a
  .word 0xf03ff01f
  .word 0x71a73afb
  .word 0x366276da
  .word 0xf473d9ff


/**
 * A 1024-bit value that is NOT relatively prime to F4.
 *
 * Full value for reference =
 * 0xfe050192e57dc8199fa8556c8104b345b1e7a0cf3701f496ea8b89a35be53ed653b50c070e9683dad6d83c72430ac46131c49506ec3c23752f6c6cadad058d7188dfc7b666b7aed729ad2e207e503c205eb284fcc501de09a2fb78c905bb0def63ac03fcc55fab5282f925064e3888eda64db2120ce8691b5bd5cd42437ed723
 */
.balign 32
simple_negative_input:
  .word 0x437ed723
  .word 0x5bd5cd42
  .word 0x0ce8691b
  .word 0xa64db212
  .word 0x4e3888ed
  .word 0x82f92506
  .word 0xc55fab52
  .word 0x63ac03fc
  .word 0x05bb0def
  .word 0xa2fb78c9
  .word 0xc501de09
  .word 0x5eb284fc
  .word 0x7e503c20
  .word 0x29ad2e20
  .word 0x66b7aed7
  .word 0x88dfc7b6
  .word 0xad058d71
  .word 0x2f6c6cad
  .word 0xec3c2375
  .word 0x31c49506
  .word 0x430ac461
  .word 0xd6d83c72
  .word 0x0e9683da
  .word 0x53b50c07
  .word 0x5be53ed6
  .word 0xea8b89a3
  .word 0x3701f496
  .word 0xb1e7a0cf
  .word 0x8104b345
  .word 0x9fa8556c
  .word 0xe57dc819
  .word 0xfe050192

/**
 * A 1024-bit value that is equal to (F4-1) modulo F4.
 *
 * This input is constructed specifically to make sure the final borrow in the
 * implementation is correctly handled.
 *
 * Full value for reference =
 * 0xfe050192e57dc8199fa8556c8104b345b1e7a0cf3701f496ea8b89a35be53ed653b50c070e9683dad6d83c72430ac46131c49506ec3c23752f6c6cadad058d7188dfc7b666b7aed729ad2e207e503c205eb284fcc501de09a2fb78c905bb0def63ac03fcc55fab5282f925064e3888eda64db2120ce8691b5bd5cd42437ed722
 */
.balign 32
edge_case_input:
  .word 0x437ed722
  .word 0x5bd5cd42
  .word 0x0ce8691b
  .word 0xa64db212
  .word 0x4e3888ed
  .word 0x82f92506
  .word 0xc55fab52
  .word 0x63ac03fc
  .word 0x05bb0def
  .word 0xa2fb78c9
  .word 0xc501de09
  .word 0x5eb284fc
  .word 0x7e503c20
  .word 0x29ad2e20
  .word 0x66b7aed7
  .word 0x88dfc7b6
  .word 0xad058d71
  .word 0x2f6c6cad
  .word 0xec3c2375
  .word 0x31c49506
  .word 0x430ac461
  .word 0xd6d83c72
  .word 0x0e9683da
  .word 0x53b50c07
  .word 0x5be53ed6
  .word 0xea8b89a3
  .word 0x3701f496
  .word 0xb1e7a0cf
  .word 0x8104b345
  .word 0x9fa8556c
  .word 0xe57dc819
  .word 0xfe050192
