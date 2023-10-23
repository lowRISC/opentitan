/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone elliptic curve P-384 ECDH shared key generation test
 *
 * Uses OTBN ECC P-384 lib to perform a scalar multiplication with a valid
 * example curve point and an example scalar. Both scalar and coordinates of
 * the curve point are contained in the .data section below.
 * The x coordinate of the resulting curve point is masked arithmetically
 * with a random value. As the x coorodinate represents the actual
 * shared key, the x coordinate and its mask are then converted from an
 * arithmetic to a boolean masking scheme.
 *
 * The result of boolean unmasking is then compared with the expected shared
 * key value.
 */

.section .text.start

p384_curve_point_valid_test:
  /* Set  pointer to x coordinate */
  la        x3, dptr_x
  la        x4, x
  sw        x4, 0(x3)

  /* Set  pointer to y coordinate */
  la        x3, dptr_y
  la        x4, x
  sw        x4, 0(x3)

  /* Init all-zero register. */
  bn.xor    w31, w31, w31

  jal       x1, p384_curve_point_valid

  ecall

.data

/* pointer to x-coordinate (dptr_x) */
.globl dptr_x
.balign 4
dptr_x:
  .zero 4

/* pointer to y-coordinate (dptr_y) */
.globl dptr_y
.balign 4
dptr_y:
  .zero 4

/* Curve point x-coordinate. */
.globl x
.balign 32
x:
  .word 0x4877f3d1
  .word 0x7b829460
  .word 0xb1cac609
  .word 0x5869de54
  .word 0xee0e2beb
  .word 0x6c30f2d8
  .word 0x47e80661
  .word 0x394d8b70
  .word 0xcf60d89e
  .word 0x1a9ea916
  .word 0xb439d701
  .word 0xca230836
  .zero 16

/* Curve point y-coordinate. */
.globl y
.balign 32
y:
  .word 0xc181f90f
  .word 0xc31ef079
  .word 0xbf3aff6e
  .word 0xc7e55880
  .word 0xec18818c
  .word 0xcea028a9
  .word 0x928c3e92
  .word 0x82b63bf3
  .word 0xd65e905d
  .word 0x68eef2d1
  .word 0x03afe2c2
  .word 0xaaafcad2
  .zero 16
