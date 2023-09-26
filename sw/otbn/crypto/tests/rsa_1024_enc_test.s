/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */


.section .text.start

/**
 * Standalone RSA 1024 encrypt
 *
 * Uses OTBN modexp bignum lib to encrypt the message from the .data segment
 * in this file with the public key consisting of e=65537 and modulus from
 * .data segment in this file.
 *
 * Copies the encrypted message to wide registers for comparison (starting at
 * w0).
 */
run_rsa_1024_enc:
  /* Init all-zero register. */
  bn.xor  w31, w31, w31

  /* Load number of limbs. */
  li    x30, 4

  /* Load pointers to modulus and Montgomery constant buffers. */
  la    x16, modulus
  la    x17, m0inv
  la    x18, RR

  /* Compute Montgomery constants. */
  jal      x1, modload

  /* Run exponentiation.
       dmem[plaintext] = dmem[ciphertext]^dmem[exp] mod dmem[modulus] */
  la       x14, plaintext
  la       x2, ciphertext
  jal      x1, modexp_65537

  /* copy all limbs of result to wide reg file */
  la       x21, ciphertext
  li       x8, 0
  loop     x30, 2
    bn.lid   x8, 0(x21++)
    addi     x8, x8, 1

  ecall

.data

/* Modulus */
.balign 32
modulus:
.word 0xc28cf49f
.word 0xb6e64c3b
.word 0xa21417f1
.word 0x34ab89fe
.word 0xe4d4c752
.word 0xe9289a03
.word 0xc8aa371c
.word 0xafb68c05

.word 0x893c882e
.word 0xa62c908d
.word 0xd23f4ebf
.word 0xea5bb198
.word 0xdb6f076f
.word 0xcfcc4b48
.word 0x75a24aa4
.word 0x7bda03fc

.word 0xcb5adf60
.word 0xbc7c20bc
.word 0x8ea4f2fe
.word 0x3ba5d46d
.word 0x21536a4e
.word 0x7f292995
.word 0xaafd0e56
.word 0xc8033b94

.word 0x127ca9e8
.word 0xa3998c2e
.word 0xecf3ecf6
.word 0xc39b1e20
.word 0xdc59f4e7
.word 0x5affc57c
.word 0x0a4536b4
.word 0x962be299


/* Message */
.balign 32
plaintext:
.word 0x206d653f
.word 0x20666f72
.word 0x74686973
.word 0x79707420
.word 0x64656372
.word 0x616e6420
.word 0x79707420
.word 0x656e6372

.word 0x796f7520
.word 0x63616e20
.word 0x756d2c20
.word 0x6269676e
.word 0x6c6c6f20
.word 0x00004865
.word 0x00000000
.word 0x00000000

.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000

.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000

/* output buffer */
.balign 32
ciphertext:
.zero 128

/* buffer for Montgomery constant RR */
.balign 32
RR:
.zero 128

/* buffer for Montgomery constant m0inv */
.balign 32
m0inv:
.zero 32
