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
 * w0). See comment at the end of the file for expected values.
 */
run_rsa_1024_enc:
  jal      x1, modload
  jal      x1, modexp_65537
  /* pointer to out buffer */
  lw        x21, 28(x0)

  /* copy all limbs of result to wide reg file */
  li       x8, 0
  loop     x30, 2
    bn.lid   x8, 0(x21++)
    addi     x8, x8, 1

  ecall


.data

/*
 * The words below are used by the code above, but the linker can't tell
 * because we reference them by absolute address. Make a global symbol
 * (cfg_data), which will refer to the whole lot and ensure that gc-sections
 * doesn't discard them.
 */
.globl cfg_data
cfg_data:

/* reserved */
.word 0x00000000

/* number of limbs (N) */
.word 0x00000004

/* pointer to m0' (dptr_m0d) */
.word 0x00000280

/* pointer to RR (dptr_rr) */
.word 0x000002c0

/* load pointer to modulus (dptr_m) */
.word 0x00000080

/* pointer to base bignum buffer (dptr_in) */
.word 0x000004c0

/* pointer to exponent buffer (dptr_exp, unused for encrypt) */
.word 0x000006c0

/* pointer to out buffer (dptr_out) */
.word 0x000008c0


/* Modulus */
/* skip to 128 */
.skip 96

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
/* skip to 1216 */
.skip 960

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
