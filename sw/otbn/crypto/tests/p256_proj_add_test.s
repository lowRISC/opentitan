/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for P-256 point addition in projective space
 *
 * Performs addition of two valid P-256 points in projective space.
 * Constant coordinates for the two points contained in the .data section.
 *
 * See comment at the end of the file for expected values of coordinates
 * of resulting point.
 */

.section .text.start

p256_proj_add_test:

  /* load curve points to w8..w13 */
  li       x2, 8
  la       x3, p1_x
  bn.lid   x2++, 0(x3)
  la       x3, p1_y
  bn.lid   x2++, 0(x3)
  la       x3, p1_z
  bn.lid   x2++, 0(x3)
  la       x3, p2_x
  bn.lid   x2++, 0(x3)
  la       x3, p2_y
  bn.lid   x2++, 0(x3)
  la       x3, p2_z
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

  /* init all-zero reg */
  bn.xor   w31, w31, w31

  jal      x1, proj_add

  ecall


.data

/* point 1 x-coordinate p1_x */
p1_x:
  .word 0xd898c296
  .word 0xf4a13945
  .word 0x2deb33a0
  .word 0x77037d81
  .word 0x63a440f2
  .word 0xf8bce6e5
  .word 0xe12c4247
  .word 0x6b17d1f2

/* point 1 y-coordinate p1_y */
p1_y:
  .word 0x37bf51f5
  .word 0xcbb64068
  .word 0x6b315ece
  .word 0x2bce3357
  .word 0x7c0f9e16
  .word 0x8ee7eb4a
  .word 0xfe1a7f9b
  .word 0x4fe342e2

/* point 1 z-coordinate p1_z */
p1_z:
  .word 0x00000001
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000

/* point 2 x-coordinate p2_x */
p2_x:
  .word 0xbfa8c334
  .word 0x9773b7b3
  .word 0xf36b0689
  .word 0x6ec0c0b2
  .word 0xdb6c8bf3
  .word 0x1628ce58
  .word 0xfacdc546
  .word 0xb5511a6a

/* point 2 y-coordinate p2_y */
p2_y:
  .word 0x9e008c2e
  .word 0xa8707058
  .word 0xab9c6924
  .word 0x7f7a11d0
  .word 0xb53a17fa
  .word 0x43dd09ea
  .word 0x1f31c143
  .word 0x42a1c697

/* point 2 z-coordinate p2_z */
p2_z:
  .word 0x00000001
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
