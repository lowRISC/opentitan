/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */


.section .text.start

/**
 * Standalone RSA-3072 modexp with secret exponent (decryption/signing).
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
0xb2e73fd1e1dce003def2f2795a1400f2514256a70fe83d64ae8464f114839c94d975c89f97b3598b48de7a560b867b4967ae92d3552f0b204c000b0841f5fac3ef0ba000acfb517a995cf708e46c670a885626d7865ebc5bccc509bc562a4ffc956eb3b859e43bc83debe4888e3e6a55de852c027a874b9c803598a78f4196800db785d91730e8708b8cef986c6d326c9a003201737cb3f5e42cd601c47d74898105671d446b9a5c8a835286f419682fc4b69e79a8d2f9f6aabca5b0c311dabe6fb19d3e03045a729b3107f21370935c6de2316876afae55aeb4da07b8a04aafc1f7717f8d571f47c1a0f395e4ce78ed581db853bda1cb6f224fc4b2c6244611d416b2e729c54ef638d7bd94483b11b56b7b613c06b2564c08de82ef33dff23892e183fd6e96713bfaf76b792c4e8071f3dd5ad695e3748179bebb97140efaabce02687b401b93a513b80b5ec334d38c0b331f90d1454c9b8f3b87017b5174f1d2b75c27fff6e89a3ae099fb0455b5cc9d3bd4840baf510e4d80dbbac4049efb
 */
.balign 32
modulus:
  .word 0xc4049efb
  .word 0x4d80dbba
  .word 0x0baf510e
  .word 0x9d3bd484
  .word 0x0455b5cc
  .word 0x3ae099fb
  .word 0xfff6e89a
  .word 0xd2b75c27
  .word 0x7b5174f1
  .word 0x8f3b8701
  .word 0xd1454c9b
  .word 0x0b331f90
  .word 0xc334d38c
  .word 0x13b80b5e
  .word 0x401b93a5
  .word 0xce02687b
  .word 0x140efaab
  .word 0x79bebb97
  .word 0x95e37481
  .word 0xf3dd5ad6
  .word 0x2c4e8071
  .word 0xfaf76b79
  .word 0x6e96713b
  .word 0x92e183fd
  .word 0x33dff238
  .word 0x08de82ef
  .word 0x06b2564c
  .word 0x6b7b613c
  .word 0x483b11b5
  .word 0x38d7bd94
  .word 0x29c54ef6
  .word 0xd416b2e7
  .word 0xc6244611
  .word 0x224fc4b2
  .word 0xbda1cb6f
  .word 0x581db853
  .word 0xe4ce78ed
  .word 0xc1a0f395
  .word 0x8d571f47
  .word 0xc1f7717f
  .word 0xb8a04aaf
  .word 0xaeb4da07
  .word 0x76afae55
  .word 0x6de23168
  .word 0x1370935c
  .word 0x9b3107f2
  .word 0x03045a72
  .word 0x6fb19d3e
  .word 0xc311dabe
  .word 0xaabca5b0
  .word 0xa8d2f9f6
  .word 0xc4b69e79
  .word 0xf419682f
  .word 0x8a835286
  .word 0x446b9a5c
  .word 0x8105671d
  .word 0xc47d7489
  .word 0xe42cd601
  .word 0x737cb3f5
  .word 0x9a003201
  .word 0x6c6d326c
  .word 0x8b8cef98
  .word 0x1730e870
  .word 0x0db785d9
  .word 0x8f419680
  .word 0x803598a7
  .word 0x7a874b9c
  .word 0xde852c02
  .word 0x8e3e6a55
  .word 0x3debe488
  .word 0x59e43bc8
  .word 0x956eb3b8
  .word 0x562a4ffc
  .word 0xccc509bc
  .word 0x865ebc5b
  .word 0x885626d7
  .word 0xe46c670a
  .word 0x995cf708
  .word 0xacfb517a
  .word 0xef0ba000
  .word 0x41f5fac3
  .word 0x4c000b08
  .word 0x552f0b20
  .word 0x67ae92d3
  .word 0x0b867b49
  .word 0x48de7a56
  .word 0x97b3598b
  .word 0xd975c89f
  .word 0x14839c94
  .word 0xae8464f1
  .word 0x0fe83d64
  .word 0x514256a7
  .word 0x5a1400f2
  .word 0xdef2f279
  .word 0xe1dce003
  .word 0xb2e73fd1

/* Base for exponentiation (corresponds to ciphertext for decryption or
   message for signing).

   Raw hex value = 
0x1273e84d4509b08a748a9bf81808f0a2387616159d3b04b32ab172285440f09f69f53e37a7cb6a6fc3fb0626a4dad7b64417570b4e112843bd3c82030fb4a01ba9ba2c194e98d51372b9a63153d7279c62452592d597c85dc493d167735918d89c4aa86d20073a0d6ce2a3bf7dc603d73efb38c5ff6fb191db117f8cf4cb0b46e995bfa0e4cee3a055fc44e496989f7248e95c6e3f4879d2c38118f51a0910d37030ddf0a39a0e6e0e3e4be9b0d12e8d25f337657e7f752fa63defebd91b2c107a00475fde78b38da4ca12c17160a8d68f6eecb60481e6ae3f3a0dc03ebb82f327dfe85f850d05215af5f7c07cd5932aaec3d17339e75b2ec803d231188942231edd8c43a6bd9b7be638da9911604a3308117ad41cf697273550765bac72a499cf21d4c4406668f569e4b002d75de22d3e5e7d5c7b33131389cffad951b362865106352780474b3c79378169c6998388e5d2782557c228f0fcf1e132e0fc2d14fe03cca340568cfb5c07a00b052304fa0923f1dfcf627a58e0ea093a97af836
 */
.balign 32
base:
  .word 0xa97af836
  .word 0x8e0ea093
  .word 0xfcf627a5
  .word 0xa0923f1d
  .word 0xb052304f
  .word 0xb5c07a00
  .word 0x340568cf
  .word 0x4fe03cca
  .word 0x2e0fc2d1
  .word 0x0fcf1e13
  .word 0x557c228f
  .word 0x8e5d2782
  .word 0x9c699838
  .word 0xc7937816
  .word 0x780474b3
  .word 0x65106352
  .word 0x951b3628
  .word 0x389cffad
  .word 0xc7b33131
  .word 0xd3e5e7d5
  .word 0x2d75de22
  .word 0x569e4b00
  .word 0x4406668f
  .word 0x9cf21d4c
  .word 0xbac72a49
  .word 0x73550765
  .word 0x41cf6972
  .word 0x308117ad
  .word 0x911604a3
  .word 0xbe638da9
  .word 0x3a6bd9b7
  .word 0x31edd8c4
  .word 0x11889422
  .word 0xec803d23
  .word 0x339e75b2
  .word 0xaaec3d17
  .word 0x07cd5932
  .word 0x15af5f7c
  .word 0xf850d052
  .word 0x327dfe85
  .word 0x03ebb82f
  .word 0xe3f3a0dc
  .word 0x60481e6a
  .word 0x68f6eecb
  .word 0x17160a8d
  .word 0xda4ca12c
  .word 0xfde78b38
  .word 0x07a00475
  .word 0xbd91b2c1
  .word 0xfa63defe
  .word 0x57e7f752
  .word 0xd25f3376
  .word 0x9b0d12e8
  .word 0xe0e3e4be
  .word 0x0a39a0e6
  .word 0x37030ddf
  .word 0x51a0910d
  .word 0x2c38118f
  .word 0xe3f4879d
  .word 0x248e95c6
  .word 0x496989f7
  .word 0x055fc44e
  .word 0x0e4cee3a
  .word 0x6e995bfa
  .word 0xcf4cb0b4
  .word 0x1db117f8
  .word 0x5ff6fb19
  .word 0x73efb38c
  .word 0xf7dc603d
  .word 0xd6ce2a3b
  .word 0xd20073a0
  .word 0x89c4aa86
  .word 0x7735918d
  .word 0xdc493d16
  .word 0x2d597c85
  .word 0xc6245259
  .word 0x153d7279
  .word 0x372b9a63
  .word 0x94e98d51
  .word 0xba9ba2c1
  .word 0x30fb4a01
  .word 0x3bd3c820
  .word 0xb4e11284
  .word 0x64417570
  .word 0x6a4dad7b
  .word 0xfc3fb062
  .word 0x7a7cb6a6
  .word 0xf69f53e3
  .word 0x85440f09
  .word 0x32ab1722
  .word 0x59d3b04b
  .word 0x23876161
  .word 0x81808f0a
  .word 0xa748a9bf
  .word 0xd4509b08
  .word 0x01273e84

/* Private exponent d =
0x1bf6782bb27d670843db3e5a0861d30a0cf86cf9dccb24796daba4e96796f0acf5566b1ec2c3d62da69c9b8b826ea92b7e88b34b53e7affa02d708e26808ee029d04f8a3d265cfc4f55eaa001a4ff54518ad3a91fa5f295ac1e55451bb380edb8071d6a66c6a778ba35e1110e506cd711180483234fb9bae60fdbf980514afd4e10ffbdc443b314192165bc6bbbfcf9f58ecc9e41f2c7126705d2fb00409c5e2ce274d882e0f1188006069504dac00f4626f56d2d637efb905d3c9a418c15c2a9f1b2f1d3fca1461d2b483d3ce354e56f24ebbea9197c2359af199d89cdaf737668626719923e8718ee4f5085ecb1b09aed5f539795ef462f173451e18d04939b2b090fdc6e75bd438be26cc7b0b8244810176d366e6f1b38144510d956f5ed8f5f3f51e50092b54945cf6ecc0a6f317cc44e487dd38f8b3e0f42841ff538d87b75d592fdca3ee5f1eedc81f0d9b2652b5058a3e50b9ab7d266eb0c681f6f829daec744b0cbf7d22d099e96cd3d1e29cb675ecaef5a7d99d35b84ca4d35c6b8d
 */
.balign 32
exp:
  .word 0xd35c6b8d
  .word 0x35b84ca4
  .word 0xf5a7d99d
  .word 0xb675ecae
  .word 0xd3d1e29c
  .word 0xd099e96c
  .word 0x0cbf7d22
  .word 0xdaec744b
  .word 0x81f6f829
  .word 0x266eb0c6
  .word 0x50b9ab7d
  .word 0xb5058a3e
  .word 0x0d9b2652
  .word 0x1eedc81f
  .word 0xdca3ee5f
  .word 0xb75d592f
  .word 0xff538d87
  .word 0xe0f42841
  .word 0xdd38f8b3
  .word 0xcc44e487
  .word 0xc0a6f317
  .word 0x945cf6ec
  .word 0x50092b54
  .word 0xf5f3f51e
  .word 0x956f5ed8
  .word 0x8144510d
  .word 0x66e6f1b3
  .word 0x810176d3
  .word 0x7b0b8244
  .word 0x38be26cc
  .word 0xc6e75bd4
  .word 0xb2b090fd
  .word 0x18d04939
  .word 0xf173451e
  .word 0x795ef462
  .word 0xaed5f539
  .word 0x5ecb1b09
  .word 0x8ee4f508
  .word 0x9923e871
  .word 0x66862671
  .word 0x9cdaf737
  .word 0x9af199d8
  .word 0x9197c235
  .word 0xf24ebbea
  .word 0xce354e56
  .word 0xd2b483d3
  .word 0x3fca1461
  .word 0x9f1b2f1d
  .word 0x18c15c2a
  .word 0x05d3c9a4
  .word 0xd637efb9
  .word 0x626f56d2
  .word 0x4dac00f4
  .word 0x00606950
  .word 0x2e0f1188
  .word 0xce274d88
  .word 0x0409c5e2
  .word 0x705d2fb0
  .word 0x1f2c7126
  .word 0x58ecc9e4
  .word 0xbbbfcf9f
  .word 0x92165bc6
  .word 0x443b3141
  .word 0xe10ffbdc
  .word 0x0514afd4
  .word 0x60fdbf98
  .word 0x34fb9bae
  .word 0x11804832
  .word 0xe506cd71
  .word 0xa35e1110
  .word 0x6c6a778b
  .word 0x8071d6a6
  .word 0xbb380edb
  .word 0xc1e55451
  .word 0xfa5f295a
  .word 0x18ad3a91
  .word 0x1a4ff545
  .word 0xf55eaa00
  .word 0xd265cfc4
  .word 0x9d04f8a3
  .word 0x6808ee02
  .word 0x02d708e2
  .word 0x53e7affa
  .word 0x7e88b34b
  .word 0x826ea92b
  .word 0xa69c9b8b
  .word 0xc2c3d62d
  .word 0xf5566b1e
  .word 0x6796f0ac
  .word 0x6daba4e9
  .word 0xdccb2479
  .word 0x0cf86cf9
  .word 0x0861d30a
  .word 0x43db3e5a
  .word 0xb27d6708
  .word 0x1bf6782b


/* output buffer */
.balign 32
result:
.zero 384

/* buffer for Montgomery constant RR */
.balign 32
RR:
.zero 384

/* buffer for Montgomery constant m0inv */
.balign 32
m0inv:
.zero 32
