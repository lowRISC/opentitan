/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for P-384 ECDSA signature generation
 *
 * Computes P-384 ECDSA signature for message, nonce and private key
 * contained in the .data section.
 *
 * See comment at the end of the file for expected values of signature.
 */

.section .text.start

p384_ecdsa_sign_test:
  /* call ECDSA signing subroutine in P-384 lib */
  jal       x1, p384_sign

  /* load signature to wregs for comparison with reference */
  li        x2, 0
  la        x3, r
  bn.lid    x2++, 0(x3)
  bn.lid    x2, 32(x3)
  li        x2, 2
  la        x3, s
  bn.lid    x2++, 0(x3)
  bn.lid    x2, 32(x3)

  ecall


.data

/* 1st scalar share k0 (448-bit) */
.globl k0
k0:
  .word 0x5c832a51
  .word 0x3eb17c27
  .word 0x9a0c1b76
  .word 0x6e001281
  .word 0x4de8344e
  .word 0x5b7d3b0f
  .word 0x96d2f9e0
  .word 0x1e9d19e7
  .word 0x16f5c1ee
  .word 0x800a4c94
  .word 0xe14cd8df
  .word 0xadb9ce1b
  .word 0x8677a5f2
  .word 0x32f9e2b0
  .zero 8

/* 2nd scalar share k1 (448-bit) */
.globl k1
k1:
  .word 0xe50b5e8e
  .word 0x776ad076
  .word 0x60d31f0e
  .word 0x3521b5e8
  .word 0x7bf0f8d5
  .word 0xe08231d6
  .word 0x7042f3bb
  .word 0x4cb12f81
  .word 0x82a3d7ab
  .word 0x198f4d05
  .word 0xb84cc0ba
  .word 0xebdfcb7d
  .word 0x9ec9b42f
  .word 0x9e5dc598
  .zero 8

/* nonce k = k0 + k1 mod n (n: curve order) */
nonce_k:
  .word 0x99999999
  .word 0x99999999
  .word 0x99999999
  .word 0x99999999
  .word 0x99999999
  .word 0x99999999
  .word 0x99999999
  .word 0x99999999
  .word 0x99999999
  .word 0x99999999
  .word 0x99999999
  .word 0x99999999
  .zero 16

/* 1st private key share d0 (448-bit) */
.globl d0
d0:
  .word 0x5c832a51
  .word 0x3eb17c27
  .word 0x9a0c1b76
  .word 0x6e001281
  .word 0x4de8344e
  .word 0x5b7d3b0f
  .word 0x96d2f9e0
  .word 0x1e9d19e7
  .word 0x16f5c1ee
  .word 0x800a4c94
  .word 0xe14cd8df
  .word 0xadb9ce1b
  .word 0x8677a5f2
  .word 0x32f9e2b0
  .zero 8

/* 2nd private key share d1 (448-bit) */
.globl d1
d1:
  .word 0x33eae098
  .word 0xd31b18d5
  .word 0x507568cd
  .word 0xab8fb14d
  .word 0x9ef51898
  .word 0x44676e61
  .word 0x9cb814d9
  .word 0x4ad22b6e
  .word 0x8930f243
  .word 0xb706d682
  .word 0xa9da1611
  .word 0x13e7014a
  .word 0x9ec9b430
  .word 0x9e5dc598
  .zero 8

/* private key d = d0 + d1 mod n (n: curve order) */
priv_key_d:
  .word 0xe8791ba3
  .word 0xf549e1f7
  .word 0x893be358
  .word 0x100794fe
  .word 0xbc9db95d
  .word 0xfd7ed624
  .word 0xc60ebab6
  .word 0x97ba9586
  .word 0xa026b431
  .word 0x37112316
  .word 0x8b26eef1
  .word 0xc1a0cf66
  .zero 16

/* message */
.globl msg
msg:
  .word 0x55555555
  .word 0x55555555
  .word 0x55555555
  .word 0x55555555
  .word 0x55555555
  .word 0x55555555
  .word 0x55555555
  .word 0x55555555
  .word 0x55555555
  .word 0x55555555
  .word 0x55555555
  .word 0x55555555
  .zero 16

/* signature R */
.globl r
r:
  .zero 64

/* signature S */
.globl s
s:
  .zero 64
