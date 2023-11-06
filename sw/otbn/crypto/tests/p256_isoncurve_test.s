/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for P-256 curve point test
 *
 * Runs the P-256 curve point test to check whether a point (given in affine
 * space) is a valid P-256 curve point.
 * See comment at the end of the file for expected values of result.
 */

.section .text.start

p256_oncurve_test:
  /* Initialize all-zero register. */
  bn.xor   w31, w31, w31

  /* Compute both sides of the Weierstrauss equation.
       w18 <= lhs
       w19 <= rhs */
  jal      x1, p256_isoncurve

  ecall


.data

/* buffer for right side result of Weierstrass equation */
.globl r
.balign 32
r:
  .zero 32

/* buffer for left side result of Weierstrass equation */
.globl s
.balign 32
s:
  .zero 32

/* point affine x-coordinate */
.globl x
.balign 32
x:
  .word 0xbfa8c334
  .word 0x9773b7b3
  .word 0xf36b0689
  .word 0x6ec0c0b2
  .word 0xdb6c8bf3
  .word 0x1628ce58
  .word 0xfacdc546
  .word 0xb5511a6a

/* point affine y-coordinate */
.globl y
.balign 32
y:
  .word 0x9e008c2e
  .word 0xa8707058
  .word 0xab9c6924
  .word 0x7f7a11d0
  .word 0xb53a17fa
  .word 0x43dd09ea
  .word 0x1f31c143
  .word 0x42a1c697
