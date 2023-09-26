/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */


.section .text.start

/**
 * Standalone RSA-2048 modexp with secret exponent (decryption/signing).
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
  la       x15, exp
  la       x2, result
  jal      x1, modexp

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

/* Base for exponentiation (corresponds to ciphertext for decryption or
   message for signing).

   Raw hex value = 
0x95fb986cd4aeee4b013effc1d183670380a9e2133ecc6a38dbbfff3f8ef20e1923a5e3741eac8772ee80f28994968fcabd6d454b7791263872bc68d97b6f4fbb76cee24f205d812ad36f2fcb6c11145943009a051c39c18c45b53ee19e51df0254b31eb991783718fb35c51dec249956bceb0276eaee88d8ecdeae2c08ac62a0018408af3923206e911a7ecf6ad786255fa69d63d333e6f44ebd3f5e6ebb7c82443c694d913e200492c89f046943f2dc7d8cf9951c6a33fa721558d1956fb552349ded082714be6a8bff775fd05162744d229fc9fac72509476bdc6434e5187bf3a1cc426cc13f0a10dcf0d15f28abcecfe5674782f232464b1a890d42b6fdd0
 */
.balign 32
base:
  .word 0x42b6fdd0
  .word 0x4b1a890d
  .word 0x82f23246
  .word 0xcfe56747
  .word 0x5f28abce
  .word 0x10dcf0d1
  .word 0x6cc13f0a
  .word 0xf3a1cc42
  .word 0x34e5187b
  .word 0x476bdc64
  .word 0xfac72509
  .word 0x4d229fc9
  .word 0xd0516274
  .word 0x8bff775f
  .word 0x2714be6a
  .word 0x349ded08
  .word 0x956fb552
  .word 0x721558d1
  .word 0x1c6a33fa
  .word 0x7d8cf995
  .word 0x6943f2dc
  .word 0x92c89f04
  .word 0x913e2004
  .word 0x443c694d
  .word 0x6ebb7c82
  .word 0x4ebd3f5e
  .word 0xd333e6f4
  .word 0x5fa69d63
  .word 0x6ad78625
  .word 0x911a7ecf
  .word 0x3923206e
  .word 0x018408af
  .word 0x08ac62a0
  .word 0xecdeae2c
  .word 0xeaee88d8
  .word 0xbceb0276
  .word 0xec249956
  .word 0xfb35c51d
  .word 0x91783718
  .word 0x54b31eb9
  .word 0x9e51df02
  .word 0x45b53ee1
  .word 0x1c39c18c
  .word 0x43009a05
  .word 0x6c111459
  .word 0xd36f2fcb
  .word 0x205d812a
  .word 0x76cee24f
  .word 0x7b6f4fbb
  .word 0x72bc68d9
  .word 0x77912638
  .word 0xbd6d454b
  .word 0x94968fca
  .word 0xee80f289
  .word 0x1eac8772
  .word 0x23a5e374
  .word 0x8ef20e19
  .word 0xdbbfff3f
  .word 0x3ecc6a38
  .word 0x80a9e213
  .word 0xd1836703
  .word 0x013effc1
  .word 0xd4aeee4b
  .word 0x95fb986c

/* Private exponent d =
0x51a84a52295a7da34ac3abe746edfd3e7651fdaa3be2b8340124878fe99bafe4130072934e700e537965ebac60e51918cc9b4143627050a95435703cac011974cd200aaf18a4c3242241cbe924eb0bce6357a98bf2d2e39b660128de1f2ca5747e7b5d23d906f68c398ec9f8d13e5f86f623a0dd6b03dec403f71b03207502fbb6c7d812f391e010cbed264655d11ab63c262a803196a128df72ecf1c65ed7f742371e4c4ee355f44cfae81ec0a256da9aa3eb1935fc509d366de08c7edb522411670cd7ee0053bb9395ac4cbe0af6f3cdd1c24e225ee47aa4f381764cfab389db993fed537f397fbff31362a85872993bc467dde42b66894f4cb3ce712b2ee1
 */
.balign 32
exp:
  .word 0x712b2ee1
  .word 0x4f4cb3ce
  .word 0xe42b6689
  .word 0x3bc467dd
  .word 0xa8587299
  .word 0xbff31362
  .word 0x537f397f
  .word 0xdb993fed
  .word 0x4cfab389
  .word 0xa4f38176
  .word 0x225ee47a
  .word 0xcdd1c24e
  .word 0xbe0af6f3
  .word 0x9395ac4c
  .word 0xee0053bb
  .word 0x11670cd7
  .word 0x7edb5224
  .word 0x366de08c
  .word 0x35fc509d
  .word 0x9aa3eb19
  .word 0xc0a256da
  .word 0x4cfae81e
  .word 0x4ee355f4
  .word 0x42371e4c
  .word 0xc65ed7f7
  .word 0xdf72ecf1
  .word 0x3196a128
  .word 0x3c262a80
  .word 0x55d11ab6
  .word 0xcbed2646
  .word 0xf391e010
  .word 0xb6c7d812
  .word 0x207502fb
  .word 0x03f71b03
  .word 0x6b03dec4
  .word 0xf623a0dd
  .word 0xd13e5f86
  .word 0x398ec9f8
  .word 0xd906f68c
  .word 0x7e7b5d23
  .word 0x1f2ca574
  .word 0x660128de
  .word 0xf2d2e39b
  .word 0x6357a98b
  .word 0x24eb0bce
  .word 0x2241cbe9
  .word 0x18a4c324
  .word 0xcd200aaf
  .word 0xac011974
  .word 0x5435703c
  .word 0x627050a9
  .word 0xcc9b4143
  .word 0x60e51918
  .word 0x7965ebac
  .word 0x4e700e53
  .word 0x13007293
  .word 0xe99bafe4
  .word 0x0124878f
  .word 0x3be2b834
  .word 0x7651fdaa
  .word 0x46edfd3e
  .word 0x4ac3abe7
  .word 0x295a7da3
  .word 0x51a84a52

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
