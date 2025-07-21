/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for P-384 curve point test
 *
 * Runs the P-384 curve point test to check whether a point (given in projective
 * space) is a valid P-384 curve point.
 * See comment at the end of the file for expected values of result.
 */

.section .text.start

p384_oncurve_proj_test:
  /* load domain parameter p (modulus)
     [w13, w12] = p = dmem[p384_p] */
  li        x2, 12
  la        x3, p384_p
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* Fill gpr registers with pointers to variables */
  la        x20, x
  la        x21, y
  la        x30, z

  /* call curve point test routine in P-384 lib */
  jal       x1, p384_isoncurve_proj_check

  /* load result to WDRs for comparison with reference */
  li        x2, 0
  bn.lid    x2++, 0(x22)
  bn.lid    x2++, 32(x22)
  bn.lid    x2++, 0(x23)
  bn.lid    x2++, 32(x23)

  ecall


.data

/* point projective x-coordinate */
.globl x
x:
  .word 0xe1deb3e8
  .word 0x95c4ddb2
  .word 0xb5dcf3ab
  .word 0x5236e1b9
  .word 0xfd1d90f0
  .word 0x0a41831d
  .word 0xd1293019
  .word 0x5f581967
  .word 0x4152ef02
  .word 0x1e30ae5b
  .word 0xfe36d76b
  .word 0xde71dad7
  .zero 16

/* point projective y-coordinate */
.globl y
y:
  .word 0xed9bacf5
  .word 0x656dc19b
  .word 0xdff5032a
  .word 0x7188ff4e
  .word 0x2e904769
  .word 0xe036648e
  .word 0x9c58e190
  .word 0x6d95ffcd
  .word 0x688532fe
  .word 0x138b69d6
  .word 0x67b628b1
  .word 0x6a905304
  .zero 16

/* point projective z-coordinate */
.globl z
z:
  .word 0xdab3335b
  .word 0xfff2b79b
  .word 0xa9ce9382
  .word 0xee62d2b2
  .word 0xc656bfa9
  .word 0xd2d04a0d
  .word 0xfe765c32
  .word 0xf54595e6
  .word 0xa6e59ab5
  .word 0x4cb98708
  .word 0xdc1bf490
  .word 0x1a17ea81
  .zero 16

/* buffer for right side result of Weierstrass equation */
.globl rhs
rhs:
  .zero 64

/* buffer for left side result of Weierstrass equation */
.globl lhs
lhs:
  .zero 64
