/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for a subcomponent of the Miller-Rabin primality test.
 *
 * Testing the test_witness subroutine in isolation can be helpful for
 * debugging and quick feedback.
 */

.section .text.start

main:
  /* Initialize all-zero register. */
  bn.xor    w31, w31, w31

  /* Set number of limbs (n=2).
       x30 <= n
       x31 <= n - 1 */
  li        x30, 2
  li        x31, 1

  /* Test the witness.
       w21 <= all 1s if dmem[tmp0] is possibly prime, otherwise 0 */
  la         x14, tmp0 /* witness */
  la         x15, tmp2 /* tmp buffer */
  la         x16, rsa_p
  la         x18, mont_rr
  jal        x1, test_witness

  /* Load the value from the working buffer into registers. Since the candidate
     is prime and the test should have processed all bits of (w-1) without any
     early exit, we expect that the final value will be equal to
     (witness^(rsa_p-1) * R) mod input.
       w0,w1 <= dmem[tmp2:tmp2+n*32] */
  li         x8, 0
  la         x15, tmp2
  loop       x30, 2
    bn.lid     x8, 0(x15++)
    addi       x8, x8, 1

  ecall
