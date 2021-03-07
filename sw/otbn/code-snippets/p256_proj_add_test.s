/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
 *   Standalone test for P-256 point addition in projective space
 *
 *   Performs addition of two valid P-256 points in projective space.
 *   Constant coordinates for the two points contained in the .data section.
 *
 *   See comment at the end of the file for expected values of coordinates
 *   of resulting point.
 */

.section .text

p256_proj_add_test:

  /* load points to w8..w13 */
  li       x2, 8

  /* w8 = p1_x = dmem[512] */
  bn.lid   x2++,  512(x0)

  /* w9 = p1_y = dmem[544] */
  bn.lid   x2++,  544(x0)

  /* w10 = p1_z = dmem[576] */
  bn.lid   x2++,  576(x0)

  /* w11 = p2_x = dmem[608] */
  bn.lid   x2++,  608(x0)

  /* w12 = p2_y = dmem[640] */
  bn.lid   x2++,  640(x0)

  /* w13 = p2_z = dmem[672] */
  bn.lid   x2,  672(x0)


  /* load domain parameter b
     w27 = b */
  li       x2, 27
  bn.lid   x2,  0(x0)

  /* load Barrett constant u
     w28 = u */
  li       x2, 28
  bn.lid   x2,  64(x0)


  /* load domain parameter p (modulus)
     w29 = p */
  li       x2, 29
  bn.lid   x2,  32(x0)
  /* store modulus to MOD WSR */
  bn.wsrw   0, w29


  /* init all-zero reg */
  bn.xor   w31, w31, w31

  jal      x1, proj_add

  ecall


.data

/* P-256 domain parameter b */
.word 0x27d2604b
.word 0x3bce3c3e
.word 0xcc53b0f6
.word 0x651d06b0
.word 0x769886bc
.word 0xb3ebbd55
.word 0xaa3a93e7
.word 0x5ac635d8

/* P-256 domain parameter p (modulus) */
.word 0xffffffff
.word 0xffffffff
.word 0xffffffff
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000001
.word 0xffffffff

/* barrett constant u for modulus p */
.word 0x00000003
.word 0x00000000
.word 0xffffffff
.word 0xfffffffe
.word 0xfffffffe
.word 0xfffffffe
.word 0xffffffff
.word 0x00000000

.skip 416

/* point 1 x-cooridante p1_x*/
.word 0xd898c296
.word 0xf4a13945
.word 0x2deb33a0
.word 0x77037d81
.word 0x63a440f2
.word 0xf8bce6e5
.word 0xe12c4247
.word 0x6b17d1f2

/* point 1 y-cooridante p1_y*/
.word 0x37bf51f5
.word 0xcbb64068
.word 0x6b315ece
.word 0x2bce3357
.word 0x7c0f9e16
.word 0x8ee7eb4a
.word 0xfe1a7f9b
.word 0x4fe342e2

/* point 1 z-cooridante p1_z*/
.word 0x00000001
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000

/* point 2 x-cooridante p2_x*/
.word 0xbfa8c334
.word 0x9773b7b3
.word 0xf36b0689
.word 0x6ec0c0b2
.word 0xdb6c8bf3
.word 0x1628ce58
.word 0xfacdc546
.word 0xb5511a6a

/* point 2 y-cooridante p2_y*/
.word 0x9e008c2e
.word 0xa8707058
.word 0xab9c6924
.word 0x7f7a11d0
.word 0xb53a17fa
.word 0x43dd09ea
.word 0x1f31c143
.word 0x42a1c697

/* point 2 z-cooridante p2_z*/
.word 0x00000001
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000

/* Expected values wide register file (x-, y-, z-coordinates of result):
 w11 = 0x592e1828fe28da49f90aede1688474f4f4c68bc0c51666812bf63ea329945969
 w12 = 0x3c57a35821690579a8e27ec0be7a3f100403f120312cf5b879e2f76f790331d7
 w13 = 0x20ee7815f61cb7b460e062016694a5411f852e298f26d449f355e47a9f192e78
 */
