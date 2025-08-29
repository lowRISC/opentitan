/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for P-384 ECDSA signature generation
 *
 * Computes P-384 ECDSA signature for message, nonce and private key
 * contained in the .data section.
 *
 * See comment at the end of the file for expected values of signature.
 */

.section .text.start

p384_ecdsa_sign_test:
  /* call ECDSA signing subroutine in P-384 lib */
  jal       x1, p384_sign

  /* load signature to wregs for comparison with reference */
  li        x2, 0
  la        x3, r
  bn.lid    x2++, 0(x3)
  bn.lid    x2, 32(x3)
  li        x2, 2
  la        x3, s
  bn.lid    x2++, 0(x3)
  bn.lid    x2, 32(x3)

  ecall
