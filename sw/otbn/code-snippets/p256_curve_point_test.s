/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone elliptic curve P-256 curve point test
 *
 * Uses OTBN ECC P-256 lib to check if a curve point is on the P-256 curve. The
 * point is on the curve if the R and S return values are identical. The test
 * uses an example point which is on the curve. The point's coordinates are
 * contained in the .data section below.
 *
 * R and S are copied to the wide registers. See comment at the end of the file
 * for expected values for the example point.
 */

.text

curve_point_test:
  jal      x1, p256init
  jal      x1, p256isoncurve

  /* pointer to R */
  lw        x21, 12(x0)
  /* pointer to S */
  lw        x22, 16(x0)

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

/* example curve point x-coordinate */
.skip 160
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

/* Expected values wide register file (w0=R, w1=S):
w0 = 0xb103b614b389c6b8e1a08330a6ce0b9c4b3726ec0bf61f6bdd66af03a4af5660
w1 = 0xb103b614b389c6b8e1a08330a6ce0b9c4b3726ec0bf61f6bdd66af03a4af5660
*/
