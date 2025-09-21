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
  la         x17, mont_rr
  jal        x1, test_witness

  ecall
