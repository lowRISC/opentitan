/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone elliptic curve P-256 ECDH shared key generation test
 *
 * Uses OTBN ECC P-256 lib to perform a scalar multiplication with a valid
 * example curve point and an example scalar. Both scalar and coordinates of
 * the curve point are contained in the .data section below.
 * The x coordinate of the resulting curve point is masked arithmetically
 * with a random value. As the x coorodinate represents the actual
 * shared key, the x coordinate and its mask are then converted from an
 * arithmetic to a boolean masking scheme.
 *
 * The result of arithmetical unmasking as well as the result of boolean
 * unmasking are compared with an expected value.
 */

.section .text.start

p256_ecdh_shared_key_test:

  /* Call P-256 shared key generation to get a boolean-masked key.
       dmem[x] <= x0
       dmem[y] <= x1 */
  jal      x1, p256_shared_key

  /* Load the two shares.
       w11 <= dmem[x] = x0
       w12 <= dmem[y] = x1 */
  li        x3, 11
  la        x4, x
  bn.lid    x3++, 0(x4)
  la        x4, y
  bn.lid    x3, 0(x4)

  /* Unmask the shared key, x.
       w11 <= x0 ^ x1 = x */
  bn.xor    w11, w11, w12

  ecall


.data

/* Secret key d in arithmetic shares. */
.globl d0
.balign 32
d0:
  .word 0xfe6d1071
  .word 0x21d0a016
  .word 0xb0b2c781
  .word 0x9590ef5d
  .word 0x3fdfa379
  .word 0x1b76ebe8
  .word 0x74210263
  .word 0x1420fc41
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
.globl d1
.balign 32
d1:
  .zero 64

/* example curve point x-coordinate */
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

/* example curve point y-coordinate */
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

/* affine x-coordinate value before A2B */
.globl x_a
.balign 32
x_a:
  .zero 32
