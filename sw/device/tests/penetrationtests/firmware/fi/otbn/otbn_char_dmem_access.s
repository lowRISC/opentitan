/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
    OBTN.CHAR.DMEM_LOAD FI Penetration Test
*/
.section .text.start
  la x2, values
  li x1, 0

  loopi 100, 1
    nop

  bn.lid    x1++, 0x000(x2)
  bn.lid    x1++, 0x020(x2)
  bn.lid    x1++, 0x040(x2)
  bn.lid    x1++, 0x060(x2)
  bn.lid    x1++, 0x080(x2)
  bn.lid    x1++, 0x0a0(x2)
  bn.lid    x1++, 0x0c0(x2)
  bn.lid    x1++, 0x0e0(x2)
  bn.lid    x1++, 0x100(x2)
  bn.lid    x1++, 0x120(x2)
  bn.lid    x1++, 0x140(x2)
  bn.lid    x1++, 0x160(x2)
  bn.lid    x1++, 0x180(x2)
  bn.lid    x1++, 0x1a0(x2)
  bn.lid    x1++, 0x1c0(x2)
  bn.lid    x1++, 0x1e0(x2)
  bn.lid    x1++, 0x200(x2)
  bn.lid    x1++, 0x220(x2)
  bn.lid    x1++, 0x240(x2)
  bn.lid    x1++, 0x260(x2)
  bn.lid    x1++, 0x280(x2)
  bn.lid    x1++, 0x2a0(x2)
  bn.lid    x1++, 0x2c0(x2)
  bn.lid    x1++, 0x2e0(x2)
  bn.lid    x1++, 0x300(x2)
  bn.lid    x1++, 0x320(x2)
  bn.lid    x1++, 0x340(x2)
  bn.lid    x1++, 0x360(x2)
  bn.lid    x1++, 0x380(x2)
  bn.lid    x1++, 0x3a0(x2)
  bn.lid    x1++, 0x3c0(x2)
  bn.lid    x1++, 0x3e0(x2)

  loopi 100, 1
    nop
  li        x1, 0
  bn.sid    x1++, 0x3e0(x2)
  bn.sid    x1++, 0x3c0(x2)
  bn.sid    x1++, 0x3a0(x2)
  bn.sid    x1++, 0x380(x2)
  bn.sid    x1++, 0x360(x2)
  bn.sid    x1++, 0x340(x2)
  bn.sid    x1++, 0x320(x2)
  bn.sid    x1++, 0x300(x2)
  bn.sid    x1++, 0x2e0(x2)
  bn.sid    x1++, 0x2c0(x2)
  bn.sid    x1++, 0x2a0(x2)
  bn.sid    x1++, 0x280(x2)
  bn.sid    x1++, 0x260(x2)
  bn.sid    x1++, 0x240(x2)
  bn.sid    x1++, 0x220(x2)
  bn.sid    x1++, 0x200(x2)
  bn.sid    x1++, 0x1e0(x2)
  bn.sid    x1++, 0x1c0(x2)
  bn.sid    x1++, 0x1a0(x2)
  bn.sid    x1++, 0x180(x2)
  bn.sid    x1++, 0x160(x2)
  bn.sid    x1++, 0x140(x2)
  bn.sid    x1++, 0x120(x2)
  bn.sid    x1++, 0x100(x2)
  bn.sid    x1++, 0x0e0(x2)
  bn.sid    x1++, 0x0c0(x2)
  bn.sid    x1++, 0x0a0(x2)
  bn.sid    x1++, 0x080(x2)
  bn.sid    x1++, 0x060(x2)
  bn.sid    x1++, 0x040(x2)
  bn.sid    x1++, 0x020(x2)
  bn.sid    x1++, 0x000(x2)

  ecall

.data
  /*
    Since each .word is a 32-bit value stored little-endian, this is 32 bytes
    laid out in memory as 00, 01, 02, .., 1f. If loaded 256-bit little endian,
    the result will be 0x1f1e1d...020100.
  */
  .balign 32
  .globl values
  values:
    /* Address 0x000: */
    .word 0xeeeeeeee
    .word 0x07060504
    .word 0x0b0a0908
    .word 0x0f0e0d0c
    .word 0x13121110
    .word 0x17161514
    .word 0x1b1a1918
    .word 0x1f1e1d1c
    /* Address 0x020 */
    .word 0xfa6aa305
    .word 0x4bf25027
    .word 0x3c2c3c75
    .word 0x4f60fbef
    .word 0xfc5d5be5
    .word 0x45e07607
    .word 0xd4eaf866
    .word 0xac8c5968
    /* Address 0x040 */
    .word 0xd1d0238c
    .word 0xbf926173
    .word 0x7aa4459b
    .word 0x82df4fba
    .word 0xc3ed3171
    .word 0xafa3f885
    .word 0xe32bba64
    .word 0x90fe233e
    /* Address 0x060 */
    .word 0xc03ada84
    .word 0xf7a2411b
    .word 0xdc382d37
    .word 0xbe18f426
    .word 0x96cc0604
    .word 0x6b6799c2
    .word 0x505d0e77
    .word 0x2160cae8
    /* Address 0x080 */
    .word 0x54bc863a
    .word 0x679163f2
    .word 0x35a47508
    .word 0xb92482e0
    .word 0xe43d9d95
    .word 0xe26aad45
    .word 0x605023e6
    .word 0xc8bb925c
    /* Address 0x0a0 */
    .word 0xed163557
    .word 0x98bd371f
    .word 0x9cec224a
    .word 0x8a6af545
    .word 0xf8455ed4
    .word 0x665acf3a
    .word 0x0b690299
    .word 0xe543605b
    /* Address 0x0c0 */
    .word 0x15cb958f
    .word 0x6472a98f
    .word 0x5a512b04
    .word 0xcd0b8525
    .word 0xc94b94b6
    .word 0x96e16897
    .word 0xc8895ab9
    .word 0x152dbe4c
    /* Address 0x0e0 */
    .word 0xccf94503
    .word 0xd342d748
    .word 0x02f2c658
    .word 0x01abd65f
    .word 0xda5eeb22
    .word 0x2d6cbaab
    .word 0x571a839d
    .word 0x9469e967
    /* Address 0x100 */
    .word 0xf510061b
    .word 0xbec0536f
    .word 0x78448c7a
    .word 0xb1d99c89
    .word 0x928cb04e
    .word 0x4e9cf63d
    .word 0x2d69eda4
    .word 0xb4d62cb4
    /* Address 0x120 */
    .word 0x77a61161
    .word 0x75cc1b32
    .word 0xbc2a88bd
    .word 0x2355ed13
    .word 0xdce18035
    .word 0x1568ae28
    .word 0x846b2991
    .word 0x3490ade4
    /* Address 0x140 */
    .word 0x5069a4fe
    .word 0x9e61ec9e
    .word 0xca4e439f
    .word 0x28fecdc5
    .word 0x225e8c6e
    .word 0x583026a9
    .word 0x8c82b7ab
    .word 0x4086523d
    /* Address 0x160 */
    .word 0x331f6054
    .word 0x2e0c7a25
    .word 0x2fda6c25
    .word 0x7eafe001
    .word 0xcb0f4ae0
    .word 0x692f9a96
    .word 0x36d703d2
    .word 0xefee445d
    /* Address 0x180 */
    .word 0x3de45d57
    .word 0x934311f8
    .word 0xfb755fbd
    .word 0xdf4d73c5
    .word 0x5659c824
    .word 0xc276ca89
    .word 0x6302b6e0
    .word 0x6fe7a8b1
    /* Address 0x1a0 */
    .word 0xc94bbff7
    .word 0xc4b09004
    .word 0xc20e470b
    .word 0xc677098e
    .word 0xa83713fd
    .word 0xc3ca25b6
    .word 0xfc1feb7e
    .word 0x312e622e
    /* Address 0x1c0 */
    .word 0x3b98dd07
    .word 0x0de57522
    .word 0xbbc42b94
    .word 0x20ac185d
    .word 0xbf4bf36e
    .word 0xe7cbc776
    .word 0xa4d46e9d
    .word 0xd4a1c273
    /* Address 0x1e0 */
    .word 0x4b84019e
    .word 0xe943a915
    .word 0x4116b514
    .word 0x252dd283
    .word 0x4f320dae
    .word 0x64473bea
    .word 0x9687b795
    .word 0x057a32bf
    /* Address 0x200 */
    .word 0xd1686cd2
    .word 0xc099a878
    .word 0xa71b9fa0
    .word 0xb8c713d7
    .word 0x267d497f
    .word 0x8c69ca33
    .word 0x583d79c7
    .word 0x81768429
    /* Address 0x220 */
    .word 0x3866bb40
    .word 0xc2bc4ff1
    .word 0xbe1bb3c1
    .word 0xec48e6c4
    .word 0x34fcf348
    .word 0xd05b6e22
    .word 0x5b28f949
    .word 0x9ae81d2e
    /* Address 0x240 */
    .word 0x61ae0041
    .word 0xb8a512d7
    .word 0xd41f32f0
    .word 0x3941c129
    .word 0x7310be64
    .word 0x63a1a1d5
    .word 0x0eee3deb
    .word 0x9a246593
    /* Address 0x260 */
    .word 0x2c8fb248
    .word 0x0a09b1d2
    .word 0x067a11a4
    .word 0xffdd4528
    .word 0x2f611ede
    .word 0x855ff86e
    .word 0x167a56ea
    .word 0x30e6b89e
    /* Address 0x280 */
    .word 0x86750ae0
    .word 0xd22aa4c8
    .word 0x97311c40
    .word 0xd4babab5
    .word 0x7c1353b2
    .word 0x5a5f37cc
    .word 0x0fce50d3
    .word 0x308298b5
    /* Address 0x2a0 */
    .word 0x48ed55e0
    .word 0x3a16fc9f
    .word 0x8bba1c50
    .word 0x2db1aa22
    .word 0x73cb4559
    .word 0x43e965bb
    .word 0x047eb4b2
    .word 0x031fcace
    /* Address 0x2c0 */
    .word 0x03d74112
    .word 0xaa250aae
    .word 0xe0001ad6
    .word 0xbcade300
    .word 0xd3e9a20d
    .word 0x59387c0e
    .word 0x40ee386b
    .word 0xff700fad
    /* Address 0x2e0 */
    .word 0x635e374e
    .word 0x188b144a
    .word 0x4569c4bd
    .word 0x627dd8a6
    .word 0xb6a67672
    .word 0x7897ee48
    .word 0x64a44eeb
    .word 0x125ffab8
    /* Address 0x300 */
    .word 0xbc0afc35
    .word 0xda6e551e
    .word 0xb28288ee
    .word 0x1bb6a1d6
    .word 0xa5eed9f4
    .word 0x00777753
    .word 0xc36fe559
    .word 0x5bba215a
    /* Address 0x320 */
    .word 0x747d6d3e
    .word 0x4ed1128d
    .word 0xf6662e91
    .word 0xa4bd7d21
    .word 0x8320954a
    .word 0xdc53ab50
    .word 0x0d54f79c
    .word 0x700135f3
    /* Address 0x340 */
    .word 0x851f978c
    .word 0x55d5c1a4
    .word 0x7d512f4f
    .word 0xfb8070ed
    .word 0xd84d0218
    .word 0x782a3321
    .word 0x1d9d1c2b
    .word 0x7d33e0db
    /* Address 0x360 */
    .word 0x9c1be92c
    .word 0x792c41b0
    .word 0x40b5b236
    .word 0x9f42454b
    .word 0x60bbb6e3
    .word 0x71fb8fae
    .word 0xca2421c9
    .word 0xfdb27cdc
    /* Address 0x380 */
    .word 0x8e43137e
    .word 0xc744c51a
    .word 0x88b7f4ed
    .word 0x86de6a48
    .word 0x2c996256
    .word 0x538607bd
    .word 0x3026c936
    .word 0xde53ffd6
    /* Address 0x3a0 */
    .word 0xf0449e22
    .word 0x7806fc6e
    .word 0x35490afa
    .word 0x4e2f74b9
    .word 0x5527567f
    .word 0xf59a9351
    .word 0xf1ce2e82
    .word 0xef9cdbba
    /* Address 0x3c0 */
    .word 0x5d7b6326
    .word 0x7c2e02c0
    .word 0x310a9d5a
    .word 0x571110b6
    .word 0x9360891a
    .word 0x5eedd494
    .word 0xce6185bd
    .word 0xa29720ce
    /* Address 0x3e0 */
    .word 0x6870007a
    .word 0xcbc8c93e
    .word 0x2df95a26
    .word 0xef048af4
    .word 0x940a38bf
    .word 0x27c49143
    .word 0xf6e7246d
    .word 0x0f6ecb03
