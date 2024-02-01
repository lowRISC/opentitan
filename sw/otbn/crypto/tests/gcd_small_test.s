/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Small test for GCD (example 14.55 from HAC).
*/

.section .text.start

/* Entry point. */
.globl main
main:
  /* Init all-zero register. */
  bn.xor  w31, w31, w31

  /* Input/output limb count (1). */
  li      x30, 1

  /* dmem[y] <= gcd(dmem[x], dmem[y]) */
  la      x10, x
  la      x11, y
  jal     x1, gcd

  /* Load result into w0.
       w0 <= dmem[y] */
  la      x2, y
  bn.lid  x0, 0(x2)

  ecall

.data

/* First input: x = 1764. */
x:
  .word 0x000006e4
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000

/* Second input: y = 868. */
y:
  .word 0x00000364
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
