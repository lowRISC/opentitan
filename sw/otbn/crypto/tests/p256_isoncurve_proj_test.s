/* Copyright lowRISC contributors (OpenTitan project). */
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

p256_oncurve_proj_test:
  /* Initialize all-zero register. */
  bn.xor   w31, w31, w31

  /* Compute both sides of the Weierstrauss equation.
       w18 <= lhs
       w19 <= rhs */
  jal      x1, p256_isoncurve_proj

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

/* point projective x-coordinate */
.globl x
.balign 32
x:
  .word 0x9212c2db
  .word 0x1f4abc57
  .word 0x9d3f29fd
  .word 0xa1c262cf
  .word 0xa626f145
  .word 0xd69046ab
  .word 0xf2c9e102
  .word 0x353043ae

/* point projective y-coordinate */
.globl y
.balign 32
y:
  .word 0xe35ec65c
  .word 0x031a25ab
  .word 0x368f7a3c
  .word 0x3139dbcb
  .word 0xecf31fb0
  .word 0x5f8fde32
  .word 0xa81acdf6
  .word 0xad2b637b

/* point projective z-coordinate */
.globl z
.balign 32
z:
  .word 0xb94a60b5
  .word 0x67dcdbf7
  .word 0x1ab6b4ea
  .word 0x2cc7c056
  .word 0x1e38fa00
  .word 0x127d6735
  .word 0xc96a8cc6
  .word 0x2be5211f
