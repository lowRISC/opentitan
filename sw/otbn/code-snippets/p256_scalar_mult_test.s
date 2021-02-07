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

.text

scalar_mult_test:
  jal      x1, p256_init
  jal      x1, p256_scalarmult

  /* pointer to x-coordinate */
  lw        x21, 20(x0)
  /* pointer to y-coordinate */
  lw        x22, 24(x0)

  /* copy result to wide reg file */
  li       x8, 0
  bn.lid   x8, 0(x21)
  li       x9, 1
  bn.lid   x9, 0(x22)

  ecall


.data

/* pointer to k (dptr_k) */
.word 0x00000020

/* pointer to rnd (dptr_rnd) */
.word 0x00000040

/* pointer to msg (dptr_msg) */
.word 0x00000060

/* pointer to R (dptr_r) */
.word 0x00000080

/* pointer to S (dptr_s) */
.word 0x000000a0

/* pointer to X (dptr_x) */
.word 0x000000c0

/* pointer to Y (dptr_y) */
.word 0x000000e0

/* pointer to D (dptr_d) */
.word 0x00000100

/* example scalar */
.word 0xfe6d1071
.word 0x21d0a016
.word 0xb0b2c781
.word 0x9590ef5d
.word 0x3fdfa379
.word 0x1b76ebe8
.word 0x74210263
.word 0x1420fc41

/* example curve point x-coordinate */
.skip 128
.word 0xbfa8c334
.word 0x9773b7b3
.word 0xf36b0689
.word 0x6ec0c0b2
.word 0xdb6c8bf3
.word 0x1628ce58
.word 0xfacdc546
.word 0xb5511a6a

/* example curve point y-coordinate */
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
