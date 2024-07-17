/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */


/**
 * Randomizable bignum multiply test.
 *
 * The following buffers are generated separately by the test infrastructure:
 *   x: 64 bytes
 *   y: 64 bytes
 */

.section .text.start
main:
  /* Init all-zero register. */
  bn.xor  w31, w31, w31

  /* Operand limb count (2). */
  li      x30, 2

  /* dmem[result] <= mul(dmem[x], dmem[y]) */
  la      x10, x
  la      x11, y
  la      x12, result
  jal     x1, bignum_mul

  /* Load result into w0 through w3.
       [w0..w3] <= dmem[result] */
  la      x2, result
  li      x3, 0
  bn.lid  x3, 0(x2++)
  addi    x3, x3, 1
  bn.lid  x3, 0(x2++)
  addi    x3, x3, 1
  bn.lid  x3, 0(x2++)
  addi    x3, x3, 1
  bn.lid  x3, 0(x2)

  ecall

.data

/* Buffer to hold the multiplication result. */
.balign 32
result:
.zero 128
