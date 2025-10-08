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

  /* w22 <= 0 if dmem[tmp0] is NOT relatively prime to F4 */
  la        x16, r0
  jal       x1, relprime_f4_test

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

  /* w22 <= 0 if dmem[tmp2] is NOT relatively prime to F4 */
  la        x16, r1
  jal       x1, relprime_f4_test

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

  /* w22 <= 0 if dmem[tmp4] is NOT relatively prime to F4 */
  la        x16, r2
  jal       x1, relprime_f4_test

  /* w23 <= ~w31 = 2^256-1 (failure value) */
  bn.not    w23, w31

  /* FG0.Z <= (w22 == 0) */
  bn.add    w22, w22, w31

  /* We expect a nonzero value in w22, since the input is relatively prime.
      w2 <= (w22 == 0) ? 2^256-1 (failure) : 0 (success) */
  bn.sel    w2, w23, w31, FG0.Z

  ret
