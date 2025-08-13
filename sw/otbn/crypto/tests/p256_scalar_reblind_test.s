/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for P256 scalar hiding.
 */

.section .text.start

p256_scalar_reblind_test:
  /* Init all-zero register. */
  bn.xor    w31, w31, w31

  /* [w1, w0] <= scalar0 */
  la        x16, scalar0
  li        x2, 0
  bn.lid    x2, 0(x16++)
  li        x2, 1
  bn.lid    x2, 0(x16)

  /* [w3, w2] <= scalar1 */
  la        x16, scalar1
  li        x2, 2
  bn.lid    x2, 0(x16++)
  li        x2, 3
  bn.lid    x2, 0(x16)

  /* Hide the masked scalar. */
  jal       x1, p256_masked_scalar_reblind

  ecall

.data

/* Scalar (321 bits). */
.balign 32
scalar0:
  .word 0x2335f23f
  .word 0x3c174a16
  .word 0x128c1339
  .word 0xc48e8981
  .word 0x7843d9a2
  .word 0xbb6a0205
  .word 0x446984cc
  .word 0xa210c4be
  .word 0xd7c77320
  .word 0x2bac5b0b
  .word 0x00000001
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000

scalar1:
  .word 0x2335f23f
  .word 0x3c174a16
  .word 0x128c1339
  .word 0xc48e8981
  .word 0x7843d9a2
  .word 0xbb6a0205
  .word 0x446984cc
  .word 0xa210c4be
  .word 0xd7c77320
  .word 0x2bac5b0b
  .word 0x00000001
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
