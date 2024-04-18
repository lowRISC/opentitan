/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for P-256 point doubling in projective space.
 */

.section .text.start

p256_proj_add_test:

  /* Init all-zero register. */
  bn.xor   w31, w31, w31

  /* load curve points to w8..w10 */
  li       x2, 8
  la       x3, px
  bn.lid   x2++, 0(x3)
  la       x3, py
  bn.lid   x2++, 0(x3)
  la       x3, pz
  bn.lid   x2++, 0(x3)

  /* load domain parameter b from dmem
     w27 <= b = dmem[p256_b] */
  li        x2, 27
  la        x3, p256_b
  bn.lid    x2, 0(x3)

  /* load field modulus p from dmem
     MOD <= w29 <= p = dmem[p256_p] */
  li        x2, 29
  la        x3, p256_p
  bn.lid    x2, 0(x3)

  /* store modulus to MOD WSR */
  bn.wsrw   MOD, w29

  /* Compute the constant r256 for reduction modulo p.
       w28 <= 2^256 - p = r256 */
  bn.sub   w28, w31, w29

  /* Load the other constant for reduction modulo p.
     w29 <= dmem[p256_r448] = r448 */
  li        x2, 29
  la        x3, p256_r448
  bn.lid    x2, 0(x3)

  /* Call doubling.
     (w8, w9, w10) <= P + P */
  jal      x1, proj_double

  /* Convert to affine coordinates for comparison with expected result.
       (w11, w12) <= (x, y) */
  jal       x1, proj_to_affine

  ecall


.data

/* Point X-coordinate. */
px:
.word 0x5751336f
.word 0x4e4b1cf4
.word 0x70e68481
.word 0xffab23c9
.word 0xe51bba8f
.word 0x69a0be9f
.word 0x542d5c8e
.word 0x88b13398

/* Point Y-coordinate. */
py:
.word 0x90d2f5d1
.word 0xfd59be31
.word 0x88668bd0
.word 0xe77fc463
.word 0xe5346d5f
.word 0x05338238
.word 0x7f786af9
.word 0x4126885e

/* Point Z-coordinate. */
pz:
.word 0x2b408ce3
.word 0x85284209
.word 0x4b7fce3c
.word 0xf80baf8d
.word 0x16bb02b6
.word 0xafe58540
.word 0x60e5bb67
.word 0x8d761fd1
