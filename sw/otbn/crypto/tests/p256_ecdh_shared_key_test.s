/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone elliptic curve P-256 ECDH shared key generation test
 *
 * Uses OTBN ECC P-256 lib to perform a scalar multiplication with a valid
 * example curve point and an example scalar. Both scalar and coordinates of
 * the curve point are contained in the .data section below.
 * The x and y coordinates of the resulting curve point are masked
 * arithmetically with random values and then converted from an arithmetic
 * to a boolean masking scheme.
 *
 * The results of boolean unmasking of both coordinates are compared with the
 * expected values. In addition, the unmasked point is checked to satisfy the
 * curve equation, i.e. that the x- and y-coordinates belong to each other.
 */

.section .text.start

p256_ecdh_shared_key_test:

  /* Call P-256 shared key generation to get a boolean-masked key.
       dmem[ecdh_x0] <= x0
       dmem[ecdh_x1] <= x1
       dmem[ecdh_y0] <= y0
       dmem[ecdh_y1] <= y1 */
  jal      x1, p256_shared_key

  /* Load the shares of both coordinates.
       w11 <= dmem[ecdh_x0] = x0
       w12 <= dmem[ecdh_x1] = x1
       w13 <= dmem[ecdh_y0] = y0
       w14 <= dmem[ecdh_y1] = y1 */
  li        x3, 11
  la        x4, ecdh_x0
  bn.lid    x3++, 0(x4)
  la        x4, ecdh_x1
  bn.lid    x3++, 0(x4)
  la        x4, ecdh_y0
  bn.lid    x3++, 0(x4)
  la        x4, ecdh_y1
  bn.lid    x3, 0(x4)

  /* Unmask the shared key coordinates.
       w11 <= x0 ^ x1 = x
       w12 <= y0 ^ y1 = y */
  bn.xor    w11, w11, w12
  bn.xor    w12, w13, w14

  /* Store the unmasked point for the on-curve check. The input public key
     is no longer needed.
       dmem[x] <= w11 = x
       dmem[y] <= w12 = y */
  li        x3, 11
  la        x4, x
  bn.sid    x3++, 0(x4)
  la        x4, y
  bn.sid    x3, 0(x4)

  /* Check that the unmasked coordinates belong to the same curve point by
     computing both sides of the Weierstrass equation.
       w18 <= (x^3 + ax + b) mod p
       w19 <= (y^2) mod p */
  jal       x1, p256_isoncurve

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

/* Public key z-coordinate. */
.globl z
.balign 32
z:
  .zero 32

/* affine x-coordinate value before A2B */
.globl x_a
.balign 32
x_a:
  .zero 32
