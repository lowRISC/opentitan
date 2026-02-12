/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for P-384 ECDSA signature verification
 *
 * Runs the P-384 ECDSA signature verification algorithm for message, nonce
 * and private key contained in the .data section below.
 *
 * See comment at the end of the file for expected values of result.
 */

.section .text.start

p384_ecdsa_verify_test:
  /* call ECDSA signature verification subroutine in P-384 lib */
  jal      x1, p384_verify

  /* load signature to wregs for comparison with reference */
  li        x2, 0
  la        x3, x_r
  bn.lid    x2++, 0(x3)
  bn.lid    x2, 32(x3)

  ecall
