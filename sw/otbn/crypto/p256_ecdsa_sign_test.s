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

.section .text.start

ecdsa_sign_test:

  /* call ECDSA signing subroutine in P-256 lib */
  jal      x1, p256_sign

  /* load signature to wregs for comparison with reference */
  li        x2, 0
  la        x3, r
  bn.lid    x2, 0(x3)
  li        x2, 1
  la        x3, s
  bn.lid    x2, 0(x3)

  ecall


.data

/* first share of nonce k (first 128 bits of k, then 128 0s) */
.globl k0
.balign 32
k0:
  .word 0xfe6d1071
  .word 0x21d0a016
  .word 0xb0b2c781
  .word 0x9590ef5d
  .zero 16

/* second share of nonce k (128 0s, then last 128 bits of k) */
.globl k1
.balign 32
k1:
  .zero 16
  .word 0x3fdfa379
  .word 0x1b76ebe8
  .word 0x74210263
  .word 0x1420fc41

/* message digest */
.globl msg
.balign 32
msg:
  .word 0x4456fd21
  .word 0x400bdd7d
  .word 0xb54d7452
  .word 0x17d015f1
  .word 0x90d4d90b
  .word 0xb028ad8a
  .word 0x6ce90fef
  .word 0x06d71207

/* private key d */
.globl d0
.balign 32
d0:
  .word 0xc7df1a56
  .word 0xfbd94efe
  .word 0xaa847f52
  .word 0x2d869bf4
  .word 0x543b963b
  .word 0xe5f2cbee
  .word 0x9144233d
  .word 0xc0fbe256

/* second share of d (all-zero) */
.globl d1
.balign 32
d1:
  .zero 32

/* signature R */
.globl r
.balign 32
r:
  .zero 32

/* signature S */
.globl s
.balign 32
s:
  .zero 32

/* Expected values wide register file (w0=R, w1=S):
w0 = 0x815215ad7dd27f336b35843cbe064de299504edd0c7d87dd1147ea5680a9674a
w1 = 0xa3991e01c444042086e30cd999e589ad4dad9404e90a6d17d0b1051ec93fd605
*/
