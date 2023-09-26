/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */


.section .text.start

/**
 * Standalone RSA-4096 modexp with e=65537 (encryption/verification).
 */
main:
  /* Init all-zero register. */
  bn.xor  w31, w31, w31

  /* Load number of limbs. */
  li    x30, 16

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
0xb25ab5439b6a703a7ba169f099a766944a86466bd18324b2149a23564261af44f1087a7df201eb2dc9583de79d9db60edd4a17aee8ed7b9384de837d70f5f99ad91695d9c780dde5401f160ce02a6135df0ea2339617b962250cf810a2be45acd43b602eddf1be6321d236e6338272e5bd5cda251a896d1d65eb10e2308f9ba8bcf4fb0836a5439c8a86394acdf2a2a3d0b4ae41b75d52894a8d79adfd1cb8db977d42d4865cd9a426bf1156b86e541469ac5a54bc06231da1db901d548cf53f3f003f7cdeee9b1b9ca7b4049b0e36b8cc7fc6d62967ffbffa593aa5cfbb41c68df57003911cf3ba2516378eaa9ee36da6ce4b09d71f072a79615d5619c8132c5467b56eae8a5e2aaa56ac4aa5dc9f696f89dd0cd0f818cdc8b58c938b336f87179cbb52a6a2965a7fcd619a5b315d370bdefeca9cbd6ea39e853f39d39c14f797ca5c31535c89f883cdfbb3bb1934490b136e46f99d8e5411a2a8b73b2519f43d78ee5cc675dcbcfeac8ef693c09a1aa87785cb5713298fa2edfcc67497cc6dbbc5d911edf7b1b5a735f14ab1870b481cd35279c932c74902faf5f047d84e6bedb88c28fced24b3728c5d9dc1114c46bfded6531873e718372dad28aae0a3c4f06dd81542cb9192783a9107a0263c8add0f23b250472f50b18f0e7719a3ba58ba38bc9ab906f86d0507a44690aba5ee96ef1083c237f2f004bff60bc4ecfb99
 */
.balign 32
modulus:
  .word 0xc4ecfb99
  .word 0x04bff60b
  .word 0xc237f2f0
  .word 0x96ef1083
  .word 0x90aba5ee
  .word 0x0507a446
  .word 0xb906f86d
  .word 0xba38bc9a
  .word 0x19a3ba58
  .word 0xb18f0e77
  .word 0x50472f50
  .word 0xdd0f23b2
  .word 0xa0263c8a
  .word 0x783a9107
  .word 0x42cb9192
  .word 0xf06dd815
  .word 0xaae0a3c4
  .word 0x372dad28
  .word 0x1873e718
  .word 0xbfded653
  .word 0xc1114c46
  .word 0x728c5d9d
  .word 0xfced24b3
  .word 0xedb88c28
  .word 0x47d84e6b
  .word 0x02faf5f0
  .word 0xc932c749
  .word 0x1cd35279
  .word 0xb1870b48
  .word 0xa735f14a
  .word 0xedf7b1b5
  .word 0xbbc5d911
  .word 0x7497cc6d
  .word 0xa2edfcc6
  .word 0x5713298f
  .word 0xa87785cb
  .word 0x93c09a1a
  .word 0xfeac8ef6
  .word 0xc675dcbc
  .word 0x3d78ee5c
  .word 0x3b2519f4
  .word 0x11a2a8b7
  .word 0xf99d8e54
  .word 0x0b136e46
  .word 0xbb193449
  .word 0x83cdfbb3
  .word 0x535c89f8
  .word 0x97ca5c31
  .word 0xd39c14f7
  .word 0x9e853f39
  .word 0x9cbd6ea3
  .word 0x0bdefeca
  .word 0x5b315d37
  .word 0x7fcd619a
  .word 0xa6a2965a
  .word 0x179cbb52
  .word 0x8b336f87
  .word 0xc8b58c93
  .word 0xd0f818cd
  .word 0x6f89dd0c
  .word 0xa5dc9f69
  .word 0xaa56ac4a
  .word 0xae8a5e2a
  .word 0x5467b56e
  .word 0x19c8132c
  .word 0x79615d56
  .word 0xd71f072a
  .word 0xa6ce4b09
  .word 0xaa9ee36d
  .word 0x2516378e
  .word 0x911cf3ba
  .word 0x8df57003
  .word 0xcfbb41c6
  .word 0xfa593aa5
  .word 0x2967ffbf
  .word 0xcc7fc6d6
  .word 0x9b0e36b8
  .word 0x9ca7b404
  .word 0xdeee9b1b
  .word 0x3f003f7c
  .word 0x548cf53f
  .word 0xa1db901d
  .word 0xbc06231d
  .word 0x69ac5a54
  .word 0xb86e5414
  .word 0x26bf1156
  .word 0x865cd9a4
  .word 0x977d42d4
  .word 0xfd1cb8db
  .word 0x4a8d79ad
  .word 0xb75d5289
  .word 0xd0b4ae41
  .word 0xcdf2a2a3
  .word 0x8a86394a
  .word 0x36a5439c
  .word 0xbcf4fb08
  .word 0x308f9ba8
  .word 0x65eb10e2
  .word 0x1a896d1d
  .word 0xbd5cda25
  .word 0x338272e5
  .word 0x21d236e6
  .word 0xddf1be63
  .word 0xd43b602e
  .word 0xa2be45ac
  .word 0x250cf810
  .word 0x9617b962
  .word 0xdf0ea233
  .word 0xe02a6135
  .word 0x401f160c
  .word 0xc780dde5
  .word 0xd91695d9
  .word 0x70f5f99a
  .word 0x84de837d
  .word 0xe8ed7b93
  .word 0xdd4a17ae
  .word 0x9d9db60e
  .word 0xc9583de7
  .word 0xf201eb2d
  .word 0xf1087a7d
  .word 0x4261af44
  .word 0x149a2356
  .word 0xd18324b2
  .word 0x4a86466b
  .word 0x99a76694
  .word 0x7ba169f0
  .word 0x9b6a703a
  .word 0xb25ab543


/* Base for exponentiation (corresponds to plaintext for encryption or
   signature for verification).

   Raw hex value (randomly generated) =
0x9e67bf21cfb170bd70edb7b9ffb99fbfe6a681f9e17bc8a966bf55d54794b95f9c4ff3657f3eef86433035ec3cc1fd4c092498a59f3fb5ac0b29c1a7a429130509229a001a86f72182354886779211a3f38ae8b864d094f875cc30bfce8df4a999cd6e43ab25c786ebb4d78bd6f439b278937d6d092be28d986564faab071878f0b4982b70af87c2261a0fc4d58b4c5d227cd880b40af25828988a730746b711cd6aaeec67f07b40df881cc8b784f944f4dc9fccac096631baf8ec17201fbacab0f09cbd2e816495820f6a5d7263ab5dd72cee1c1145327e2696066b6103304206c29ace7f13d92b3a7edf3cb9dc3fe5d2da7c22d16319f2fcdf44a9cf14de57cc75f9395b0d1ebd90c107b74ca88d8c99be1e5a4a41d1fa2285ccd8580f4a6206fb4d0cae5945bcd33b5f1308025f660bf96e3e448216b02da98b86d8e9d633e311b2f19fce4dbaa6317d04aaf360ea9245bd0bb70811e64d87accf8ab6339b063ba26b085c85e369f37c2c62a485fab7f2b22edd5f4f6365c3e47fae372ea3e530796473835384e77187ac856b9ebbc3c10f1a0394e9a9c25a8e635a55ac907a011119aa5d00edc26f0b64e9972391ba545a03e003624e0624f824c22710237e8f97a07ffcff0106684f0c17b8df6f975bdd5f286a95f7635416b3e9129aa81e4cee9932dfe177f7f33897412fdde0e8b87f6cc0c54ab2c8f022dcb7fef768
 */
.balign 32
base:
  .word 0xb7fef768
  .word 0xc8f022dc
  .word 0xc0c54ab2
  .word 0xe8b87f6c
  .word 0x412fdde0
  .word 0xf7f33897
  .word 0x32dfe177
  .word 0x1e4cee99
  .word 0xe9129aa8
  .word 0x635416b3
  .word 0x286a95f7
  .word 0x975bdd5f
  .word 0x17b8df6f
  .word 0x06684f0c
  .word 0x7ffcff01
  .word 0x7e8f97a0
  .word 0xc2271023
  .word 0x0624f824
  .word 0xe003624e
  .word 0xba545a03
  .word 0xe9972391
  .word 0xc26f0b64
  .word 0xaa5d00ed
  .word 0x7a011119
  .word 0x5a55ac90
  .word 0xc25a8e63
  .word 0x0394e9a9
  .word 0xc3c10f1a
  .word 0x856b9ebb
  .word 0xe77187ac
  .word 0x73835384
  .word 0xe5307964
  .word 0xae372ea3
  .word 0x65c3e47f
  .word 0xdd5f4f63
  .word 0xb7f2b22e
  .word 0x62a485fa
  .word 0x69f37c2c
  .word 0x085c85e3
  .word 0x063ba26b
  .word 0x8ab6339b
  .word 0x4d87accf
  .word 0xb70811e6
  .word 0x9245bd0b
  .word 0xaaf360ea
  .word 0xa6317d04
  .word 0x9fce4dba
  .word 0xe311b2f1
  .word 0xd8e9d633
  .word 0x2da98b86
  .word 0x448216b0
  .word 0x0bf96e3e
  .word 0x08025f66
  .word 0xd33b5f13
  .word 0xae5945bc
  .word 0x06fb4d0c
  .word 0x580f4a62
  .word 0x2285ccd8
  .word 0x4a41d1fa
  .word 0x99be1e5a
  .word 0x4ca88d8c
  .word 0x90c107b7
  .word 0x5b0d1ebd
  .word 0xcc75f939
  .word 0xcf14de57
  .word 0xfcdf44a9
  .word 0xd16319f2
  .word 0xd2da7c22
  .word 0xb9dc3fe5
  .word 0x3a7edf3c
  .word 0x7f13d92b
  .word 0x06c29ace
  .word 0x61033042
  .word 0x2696066b
  .word 0x1145327e
  .word 0xd72cee1c
  .word 0x7263ab5d
  .word 0x820f6a5d
  .word 0x2e816495
  .word 0xb0f09cbd
  .word 0x201fbaca
  .word 0xbaf8ec17
  .word 0xac096631
  .word 0xf4dc9fcc
  .word 0xb784f944
  .word 0xdf881cc8
  .word 0x67f07b40
  .word 0xcd6aaeec
  .word 0x0746b711
  .word 0x28988a73
  .word 0xb40af258
  .word 0x227cd880
  .word 0xd58b4c5d
  .word 0x261a0fc4
  .word 0x70af87c2
  .word 0xf0b4982b
  .word 0xab071878
  .word 0x986564fa
  .word 0x092be28d
  .word 0x78937d6d
  .word 0xd6f439b2
  .word 0xebb4d78b
  .word 0xab25c786
  .word 0x99cd6e43
  .word 0xce8df4a9
  .word 0x75cc30bf
  .word 0x64d094f8
  .word 0xf38ae8b8
  .word 0x779211a3
  .word 0x82354886
  .word 0x1a86f721
  .word 0x09229a00
  .word 0xa4291305
  .word 0x0b29c1a7
  .word 0x9f3fb5ac
  .word 0x092498a5
  .word 0x3cc1fd4c
  .word 0x433035ec
  .word 0x7f3eef86
  .word 0x9c4ff365
  .word 0x4794b95f
  .word 0x66bf55d5
  .word 0xe17bc8a9
  .word 0xe6a681f9
  .word 0xffb99fbf
  .word 0x70edb7b9
  .word 0xcfb170bd
  .word 0x9e67bf21


/* output buffer */
.balign 32
result:
.zero 512

/* buffer for Montgomery constant RR */
.balign 32
RR:
.zero 512

/* buffer for Montgomery constant m0inv */
.balign 32
m0inv:
.zero 32
