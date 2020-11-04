/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */


.text

/**
 * Standalone RSA 1024 decrypt
 *
 * Uses OTBN modexp bignum lib to decrypt the message from the .data segment
 * in this file with the private key contained in .data segment of this file.
 *
 * Copies the decrypted message to wide registers for comparison (starting at
 * w0). See comment at the end of the file for expected values.
 */
 run_rsa_1024_dec:
  jal      x1, modload
  jal      x1, modexp
  /* pointer to out buffer */
  lw        x21, 28(x0)

  /* copy all limbs of result to wide reg file */
  li       x8, 0
  loop     x30, 2
    bn.lid   x8, 0(x21++)
    addi     x8, x8, 1

  ecall


.data

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

/* pointer to exponent buffer (dptr_exp) */
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


/* encrypted message */
/* skip to 1216 */
.skip 960

.word 0xe0e14a9b
.word 0x7ae96741
.word 0x4a430036
.word 0xcda13a47
.word 0x79524410
.word 0x3810cd51
.word 0x3b47425f
.word 0x686f3abe

.word 0x91dff899
.word 0xbfa8b284
.word 0x0539e396
.word 0xa66cf53c
.word 0xbcdc315a
.word 0x0d595811
.word 0x0a522e08
.word 0x5b9dce33

.word 0x6fde2d48
.word 0x587a618e
.word 0x6b4c0c56
.word 0x4affcc62
.word 0x6a88ead2
.word 0x991f39d0
.word 0x39f88b9a
.word 0x3c0d6626

.word 0xa3fe6181
.word 0x82f3f1f6
.word 0x43f4ed0b
.word 0x938bfd7b
.word 0x60de8b63
.word 0x8ade6cc0
.word 0x91f560d7
.word 0x35f506d1


/* private exponent */
/* skip to 1728 */
.skip 384

.word 0x93a8cd95
.word 0x24a2614b
.word 0xeeb788b3
.word 0x6dfc48e4
.word 0xca97cdc4
.word 0x41146c79
.word 0xf4ca744b
.word 0xc386c827

.word 0xd9ddaef3
.word 0xae51440f
.word 0x9741739d
.word 0x9ebad71b
.word 0x9a7a2bfd
.word 0xfbd58848
.word 0x13464f06
.word 0x17f60ed9

.word 0x1d63a0b9
.word 0x581ccd6c
.word 0x951579d6
.word 0x35a9ec64
.word 0xc3a08e32
.word 0xdd2f62e8
.word 0xc3739e4a
.word 0x01ca5c4e

.word 0x3a107e7d
.word 0xf9dacc79
.word 0x49ecbe20
.word 0x5d21e910
.word 0x9550ecb5
.word 0x511778ce
.word 0x42209f7b
.word 0x41b468dc

/* Expected decrypted Message in wide register file:
w0 = 0x656e637279707420616e642064656372797074207468697320666f72206d653f
w1 = 0x0000000000000000000048656c6c6f206269676e756d2c2063616e20796f7520
w2 = 0x0000000000000000000000000000000000000000000000000000000000000000
w3 = 0x0000000000000000000000000000000000000000000000000000000000000000
*/
