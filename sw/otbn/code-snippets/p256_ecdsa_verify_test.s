/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone elliptic curve P-256 ECDSA signature verification test
 *
 * Uses OTBN ECC P-256 lib to perform an ECDSA signature verification.
 * Coordinates of the public key, the message digest and R and S of the
 * signature are provided in the .data section below.
 *
 * Signature verification was successful, if the return values in the rnd and R
 * location are identical. The return values are copied to wide registers. See
 * comment at the end of the file for expected values for this example.
 */

.text

ecdsa_verify_test:
  jal      x1, p256_init
  jal      x1, p256_verify

  /* pointer to rnd */
  lw        x21, 4(x0)
  /* pointer to R */
  lw        x22, 12(x0)

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

/* message digest */
.skip 64
.word 0x4456fd21
.word 0x400bdd7d
.word 0xb54d7452
.word 0x17d015f1
.word 0x90d4d90b
.word 0xb028ad8a
.word 0x6ce90fef
.word 0x06d71207

/* signature R */
.word 0x80a9674a
.word 0x1147ea56
.word 0x0c7d87dd
.word 0x99504edd
.word 0xbe064de2
.word 0x6b35843c
.word 0x7dd27f33
.word 0x815215ad

/* signature S */
.word 0xc93fd605
.word 0xd0b1051e
.word 0xe90a6d17
.word 0x4dad9404
.word 0x99e589ad
.word 0x86e30cd9
.word 0xc4440420
.word 0xa3991e01

/* public key x-coordinate */
.word 0xbfa8c334
.word 0x9773b7b3
.word 0xf36b0689
.word 0x6ec0c0b2
.word 0xdb6c8bf3
.word 0x1628ce58
.word 0xfacdc546
.word 0xb5511a6a

/* public key y-coordinate */
.word 0x9e008c2e
.word 0xa8707058
.word 0xab9c6924
.word 0x7f7a11d0
.word 0xb53a17fa
.word 0x43dd09ea
.word 0x1f31c143
.word 0x42a1c697

/* Expected values wide register file (w0=rnd, w1=R):
w0 = 0x815215ad7dd27f336b35843cbe064de299504edd0c7d87dd1147ea5680a9674a
w1 = 0x815215ad7dd27f336b35843cbe064de299504edd0c7d87dd1147ea5680a9674a
*/
