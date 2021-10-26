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

  /* set dmem pointer to nonce k */
  la       x2, nonce_k
  la       x3, dptr_k
  sw       x2, 0(x3)

  /* set dmem pointer to point to blinding parameter */
  la       x2, blinding_param
  la       x3, dptr_rnd
  sw       x2, 0(x3)

  /* set dmem pointer to point to message */
  la       x2, msg
  la       x3, dptr_msg
  sw       x2, 0(x3)

  /* set dmem pointer to point to private key d */
  la       x2, priv_key_d
  la       x3, dptr_d
  sw       x2, 0(x3)

  /* set dmem pointer to point to signature */
  la       x2, sig_r
  la       x3, dptr_r
  sw       x2, 0(x3)
  la       x2, sig_s
  la       x3, dptr_s
  sw       x2, 0(x3)

  /* call ECDSA signing subroutine in P-256 lib */
  jal      x1, p256_sign

  /* load signature to wregs for comparison with reference */
  li        x2, 0
  la        x3, sig_r
  bn.lid    x2, 0(x3)
  li        x2, 1
  la        x3, sig_s
  bn.lid    x2, 0(x3)

  ecall


.data

/* nonce k */
nonce_k:
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

/* message digest */
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
priv_key_d:
  .word 0xc7df1a56
  .word 0xfbd94efe
  .word 0xaa847f52
  .word 0x2d869bf4
  .word 0x543b963b
  .word 0xe5f2cbee
  .word 0x9144233d
  .word 0xc0fbe256

/* signature R */
sig_r:
  .zero 32

/* signature S */
sig_s:
  .zero 32

/* Expected values wide register file (w0=R, w1=S):
w0 = 0x815215ad7dd27f336b35843cbe064de299504edd0c7d87dd1147ea5680a9674a
w1 = 0xa3991e01c444042086e30cd999e589ad4dad9404e90a6d17d0b1051ec93fd605
*/
