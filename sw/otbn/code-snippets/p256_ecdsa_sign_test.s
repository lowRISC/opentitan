/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone elliptic curve P-256 ECDSA sign test
 *
 * Uses OTBN ECC P-256 lib to perform an ECDSA signing operation.
 * An example message digest, the private signing key and a random value k are
 * provided in the .data section below. Note that this test does not yet use
 * OTBN's entropy interface as a source for the random value in the ECDSA
 * operation.
 *
 * Resulting R and S of the signature are copied to the wide registers. See
 * comment at the end of the file for expected values.
 */

.text

ecdsa_sign_test:
  jal      x1, p256init
  jal      x1, p256sign

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

/* example random scalar k */
.word 0xfe6d1071
.word 0x21d0a016
.word 0xb0b2c781
.word 0x9590ef5d
.word 0x3fdfa379
.word 0x1b76ebe8
.word 0x74210263
.word 0x1420fc41

/* message digest */
.skip 32
.word 0x4456fd21
.word 0x400bdd7d
.word 0xb54d7452
.word 0x17d015f1
.word 0x90d4d90b
.word 0xb028ad8a
.word 0x6ce90fef
.word 0x06d71207

/* private key d */
.skip 128
.word 0xc7df1a56
.word 0xfbd94efe
.word 0xaa847f52
.word 0x2d869bf4
.word 0x543b963b
.word 0xe5f2cbee
.word 0x9144233d
.word 0xc0fbe256

/* Expected values wide register file (w0=R, w1=S):
w0 = 0x815215ad7dd27f336b35843cbe064de299504edd0c7d87dd1147ea5680a9674a
w1 = 0xa3991e01c444042086e30cd999e589ad4dad9404e90a6d17d0b1051ec93fd605
*/
