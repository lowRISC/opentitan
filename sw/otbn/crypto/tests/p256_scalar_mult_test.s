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
 * x coordinate of the resulting curve points is copied to a wide
 * register.
 */

.section .text.start

scalar_mult_test:

  /* call scalar point multiplication routine in P-256 lib */
  jal      x1, p256_scalar_mult

  /* copy result to wide reg file */
  li       x2, 0
  la       x3, x
  bn.lid   x2, 0(x3)

  /* load mask */
  li       x2, 19
  la       x3, y
  bn.lid   x2, 0(x3)

  /* unmask x coordinate
     w0 <= dmem[x] + dmem[m_x] mod p */
  bn.addm    w0, w0, w19

  ecall


.data

/* scalar k */
.globl k0
.balign 32
k0:
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
.globl k1
.balign 32
k1:
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
