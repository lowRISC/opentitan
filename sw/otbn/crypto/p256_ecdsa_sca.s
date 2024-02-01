/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Elliptic curve P-256 ECDSA
 *
 * Uses OTBN ECC P-256 lib to perform an ECDSA operations.
 */

.section .text.start
.globl start
start:
  /* Read mode, then tail-call either p256_ecdsa_sign or p256_ecdsa_verify */
  la    x2, mode
  lw    x2, 0(x2)

  li    x3, 1
  beq   x2, x3, p256_ecdsa_sign

  li    x3, 2
  beq   x2, x3, p256_ecdsa_verify

  /* Mode is neither 1 (= sign) nor 2 (= verify). Fail. */
  unimp

.text
p256_ecdsa_sign:
  jal      x1, p256_sign
  ecall

p256_ecdsa_verify:
  jal      x1, p256_verify
  ecall

.data

/* Freely available DMEM space. */

/* Operation mode (1 = sign; 2 = verify) */
.globl mode
.balign 4
mode:
  .word 0x1

/* All constants below must be 256b-aligned. */

/* random scalar k (in two shares) */
.global k0
.balign 32
k0:
  /* k0 = 0x0000000...ffffffff */
  /* Note: Byte order in a word is little-endian */
  .word 0xffffffff
  .word 0xffffffff
  .word 0xffffffff
  .word 0xffffffff
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000

.global k1
.balign 32
k1:
  /* k1= 0x0000000...00000000 */
  /* Note: Byte order in a word is little-endian */
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000

/* message digest */
.globl msg
.balign 32
msg:
  /* msg = "Hello OTBN."*/
  /* msg = 0x06d71207...4456fd21 */
  /* Note: Byte order in a word is little-endian */
  .word 0x4456fd21
  .word 0x400bdd7d
  .word 0xb54d7452
  .word 0x17d015f1
  .word 0x90d4d90b
  .word 0xb028ad8a
  .word 0x6ce90fef
  .word 0x06d71207

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

/* public key x-coordinate */
.globl x
.balign 32
x:
  /* x = 0x6b17d1f2...d898c296 */
  /* Note: Byte order in a word is little-endian */
  .word 0xd898c296
  .word 0xf4a13945
  .word 0x2deb33a0
  .word 0x77037d81
  .word 0x63a440f2
  .word 0xf8bce6e5
  .word 0xe12c4247
  .word 0x6b17d1f2

/* public key y-coordinate */
.globl y
.balign 32
y:
  /* y= 0x4fe342e2...37bf51f5 */
  /* Note: Byte order in a word is little-endian */
  .word  0x37bf51f5
  .word  0xcbb64068
  .word  0x6b315ece
  .word  0x2bce3357
  .word  0x7c0f9e16
  .word  0x8ee7eb4a
  .word  0xfe1a7f9b
  .word  0x4fe342e2

/* private key d (in two shares) */
.globl d0
.balign 32
d0:
  /* d0= 0x5545a0b7...af57b4cd */
  /* Note: Byte order in a word is little-endian */
  .word 0xaf57b4cd
  .word 0x744c9f1c
  .word 0x8b7e0c02
  .word 0x283e93e9
  .word 0x0d18f00c
  .word 0xda0b6cf4
  .word 0x8fe6bb7a
  .word 0x5545a0b7

.globl d1
.balign 32
d1:
  /* d1 = 0x00000000...00000000 */
  /* Note: Byte order in a word is little-endian */
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000

/* verification result x_r (aka x_1) */
.globl x_r
.balign 32
x_r:
  .zero 32
