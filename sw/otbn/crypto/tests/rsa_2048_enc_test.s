/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */


.section .text.start

/**
 * Standalone RSA-2048 modexp with e=65537 (encryption/verification).
 */
main:
  /* Init all-zero register. */
  bn.xor  w31, w31, w31

  /* Load number of limbs. */
  li    x30, 8

  /* Load pointers to modulus and Montgomery constant buffers. */
  la    x16, modulus
  la    x17, m0inv
  la    x18, RR

  /* Compute Montgomery constants. */
  jal      x1, modload

  /* Run exponentiation.
       dmem[result] = dmem[base]^dmem[exp] mod dmem[modulus] */
  la       x14, base
  la       x2, result
  jal      x1, modexp_65537

  /* copy all limbs of result to wide reg file */
  la       x21, result
  li       x8, 0
  loop     x30, 2
    bn.lid   x8, 0(x21++)
    addi     x8, x8, 1

  ecall

.data

/* Modulus n =

0xb5ed720fe7e1b4a65494e8e9421df94910811d23854cb07b08a34508b682b188b16fa70e4804b4c4f54a54ae2a10848abc9253ac7c6085e5b9abcbcd48515db1626b01df4e7f5f1c85b9ce1b4c8d0f77f3854c8bc4f350ad4d993a6815d0d62ac83b47a257adb40023e1acf003d27953f19c5cbede1af58e42ef12ad9907c20ca428f8b7dbb6f3434936b1108d17ee343d7127f8885ff2513eb834c17bf1c4ddec0d61cc26f5f683c10c0e48676608811e9341f2898f690bc9fafd3b7e46d375e2178a141faf0d637767da550de4c5b9939af133ceba7cd2734df4ad269c166180afd8c35060de8ac302ca911aa3f92d139ed1595523a7f6c201cfafed4c17b5
 */
.balign 32
modulus:
  .word 0xed4c17b5
  .word 0xc201cfaf
  .word 0x5523a7f6
  .word 0x139ed159
  .word 0x1aa3f92d
  .word 0xc302ca91
  .word 0x5060de8a
  .word 0x80afd8c3
  .word 0x269c1661
  .word 0x734df4ad
  .word 0xceba7cd2
  .word 0x939af133
  .word 0x0de4c5b9
  .word 0x7767da55
  .word 0x1faf0d63
  .word 0xe2178a14
  .word 0x7e46d375
  .word 0xc9fafd3b
  .word 0x898f690b
  .word 0x1e9341f2
  .word 0x67660881
  .word 0xc10c0e48
  .word 0x26f5f683
  .word 0xec0d61cc
  .word 0x7bf1c4dd
  .word 0x3eb834c1
  .word 0x885ff251
  .word 0x3d7127f8
  .word 0x8d17ee34
  .word 0x4936b110
  .word 0xdbb6f343
  .word 0xa428f8b7
  .word 0x9907c20c
  .word 0x42ef12ad
  .word 0xde1af58e
  .word 0xf19c5cbe
  .word 0x03d27953
  .word 0x23e1acf0
  .word 0x57adb400
  .word 0xc83b47a2
  .word 0x15d0d62a
  .word 0x4d993a68
  .word 0xc4f350ad
  .word 0xf3854c8b
  .word 0x4c8d0f77
  .word 0x85b9ce1b
  .word 0x4e7f5f1c
  .word 0x626b01df
  .word 0x48515db1
  .word 0xb9abcbcd
  .word 0x7c6085e5
  .word 0xbc9253ac
  .word 0x2a10848a
  .word 0xf54a54ae
  .word 0x4804b4c4
  .word 0xb16fa70e
  .word 0xb682b188
  .word 0x08a34508
  .word 0x854cb07b
  .word 0x10811d23
  .word 0x421df949
  .word 0x5494e8e9
  .word 0xe7e1b4a6
  .word 0xb5ed720f


/* Base for exponentiation (corresponds to plaintext for encryption or
   signature for verification).

   Raw hex value (randomly generated) =
0x6add9548af50f1bea3cb921205a5bb92ee325e01d160e3738a09aa0df7050e6051d693440f0d00cdd56cee5a748ff3b48b1df7be05808ad20068ad387b8b5e4c25c79bba9f87ef971da926f644c26d4273829fd69db71f9eded2cd1a33c367578550346ada160daa272940dd6fc10dae4a0facef437ece40130301c1b847203cc0defd3620ce89d96fa21d30ee63e458b0198adc842f68af8b462df6014955ab68f663a9b5e77caf15a517ab0931308bf9591cecc7691780a2f3bd99d3ce25433d31537e7cab1b4c07d99199e9517132188150d38d633c2b3ef6ba6fb40504e800fca580beb7a19f2315adb451be690fc4f87ea5914d28d5562dc1dce115a852
 */
.balign 32
base:
  .word 0xe115a852
  .word 0x562dc1dc
  .word 0x914d28d5
  .word 0xc4f87ea5
  .word 0x51be690f
  .word 0x2315adb4
  .word 0xbeb7a19f
  .word 0x00fca580
  .word 0xb40504e8
  .word 0x3ef6ba6f
  .word 0x8d633c2b
  .word 0x188150d3
  .word 0xe9517132
  .word 0x07d99199
  .word 0x7cab1b4c
  .word 0x3d31537e
  .word 0xd3ce2543
  .word 0xa2f3bd99
  .word 0xc7691780
  .word 0xf9591cec
  .word 0x0931308b
  .word 0x15a517ab
  .word 0xb5e77caf
  .word 0x68f663a9
  .word 0x014955ab
  .word 0x8b462df6
  .word 0x842f68af
  .word 0xb0198adc
  .word 0xee63e458
  .word 0x6fa21d30
  .word 0x20ce89d9
  .word 0xc0defd36
  .word 0xb847203c
  .word 0x130301c1
  .word 0x437ece40
  .word 0x4a0facef
  .word 0x6fc10dae
  .word 0x272940dd
  .word 0xda160daa
  .word 0x8550346a
  .word 0x33c36757
  .word 0xded2cd1a
  .word 0x9db71f9e
  .word 0x73829fd6
  .word 0x44c26d42
  .word 0x1da926f6
  .word 0x9f87ef97
  .word 0x25c79bba
  .word 0x7b8b5e4c
  .word 0x0068ad38
  .word 0x05808ad2
  .word 0x8b1df7be
  .word 0x748ff3b4
  .word 0xd56cee5a
  .word 0x0f0d00cd
  .word 0x51d69344
  .word 0xf7050e60
  .word 0x8a09aa0d
  .word 0xd160e373
  .word 0xee325e01
  .word 0x05a5bb92
  .word 0xa3cb9212
  .word 0xaf50f1be
  .word 0x6add9548

/* output buffer */
.balign 32
result:
.zero 256

/* buffer for Montgomery constant RR */
.balign 32
RR:
.zero 256

/* buffer for Montgomery constant m0inv */
.balign 32
m0inv:
.zero 32
