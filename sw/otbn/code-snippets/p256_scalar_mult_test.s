/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone elliptic curve P-256 scalar multiplication test
 *
 * Uses OTBN ECC P-256 lib to perform a scalar multiplication with a valid
 * example curve point and an example scalar. Both scalar and coordinates of
 * the curve point are contained in the .data section below.
 *
 * x and y cordinates of the resulting curve points are copied to wide
 * registers. See comment at the end of the file for expected values.
 */

.section .text.start

scalar_mult_test:

  /* set dmem pointer to point to x-coordinate */
  la       x2, p1_x
  la       x3, dptr_x
  sw       x2, 0(x3)

  /* set dmem pointer to point to y-coordinate */
  la       x2, p1_y
  la       x3, dptr_y
  sw       x2, 0(x3)

  /* set dmem pointer to point to scalar k */
  la       x2, scalar
  la       x3, dptr_k
  sw       x2, 0(x3)

  /* set dmem pointer to point to blinding parameter */
  la       x2, blinding_param
  la       x3, dptr_rnd
  sw       x2, 0(x3)

  /* call scalar point multiplication routine in P-256 lib */
  jal      x1, p256_scalar_mult

  /* copy result to wide reg file */
  li       x2, 0
  la       x3, p1_x
  bn.lid   x2++, 0(x3)
  la       x3, p1_y
  bn.lid   x2, 0(x3)

  ecall


.data

/* scalar k */
scalar:
  .word 0xfe6d1071
  .word 0x21d0a016
  .word 0xb0b2c781
  .word 0x9590ef5d
  .word 0x3fdfa379
  .word 0x1b76ebe8
  .word 0x74210263
  .word 0x1420fc41

/* random number for blinding */
blinding_param:
  .word 0x7ab203c3
  .word 0xd6ee4951
  .word 0xd5b89b43
  .word 0x409d2b56
  .word 0x8e9d2186
  .word 0x1de0f8ec
  .word 0x0fa0bf9a
  .word 0xa21c2147

/* example curve point x-coordinate */
p1_x:
  .word 0xbfa8c334
  .word 0x9773b7b3
  .word 0xf36b0689
  .word 0x6ec0c0b2
  .word 0xdb6c8bf3
  .word 0x1628ce58
  .word 0xfacdc546
  .word 0xb5511a6a

/* example curve point y-coordinate */
p1_y:
  .word 0x9e008c2e
  .word 0xa8707058
  .word 0xab9c6924
  .word 0x7f7a11d0
  .word 0xb53a17fa
  .word 0x43dd09ea
  .word 0x1f31c143
  .word 0x42a1c697

/* Expected values wide register file (w0=X, w1=Y):
w0 = 0x5f33d746a326640a739a9490ec15c10372869f3de675b2e85742271d18c9eb82
w1 = 0xb5ebbd1e4ac99c9e3d70a862e41fe23ace6ab34f7ac9f99a4c403defb76c462d
*/
