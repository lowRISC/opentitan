/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
 *   Standalone test for P-256 scalar multiplication with base point.
 *
 *   Performs multiplication of the base point of P-256 by a scalar. This
 *   resembles computing the public key for a given private key. The scalar
 *   (private key) is contained in the .data section below.
 *
 *   See comment at the end of the file for expected values of coordinates
 *   of resulting point.
 */

.section .text.start

p256_base_mult_test:

  /* call base point multiplication routine in P-256 lib */
  jal      x1, p256_base_mult

  /* load result to WDRs for comparison with reference */
  li        x2, 0
  la        x3, x
  bn.lid    x2++, 0(x3)
  la        x3, y
  bn.lid    x2, 0(x3)

  ecall


.data

/* scalar d */
.globl d0
.balign 32
d0:
  .word 0xc7df1a56
  .word 0xfbd94efe
  .word 0xaa847f52
  .word 0x2d869bf4
  .word 0x543b963b
  .word 0xe5f2cbee
  .word 0x9144233d
  .word 0xc0fbe256
.globl d1
.balign 32
d1:
  .zero 32

/* result buffer x-coordinate */
.globl x
.balign 32
x:
  .zero 32

/* result buffer y-coordinate */
.globl y
.balign 32
y:
  .zero 32
