/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */


.section .text.start

/**
 * Standalone RSA-3072 modexp with e=65537 (encryption/verification).
 */
main:
  /* Init all-zero register. */
  bn.xor  w31, w31, w31

  /* Load number of limbs. */
  li    x30, 12

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


/* Base for exponentiation (corresponds to plaintext for encryption or
   signature for verification).

   Raw hex value (randomly generated) = 
0x77d133acf99844910deadefd84b95fc010959a01e040c559c691ac8ff0410b369453478a7ca56f74e3f6a1ea1fef9ef490d8a9c0bd385c49e7b3934e93a52e44d49a7737b8153b295d9baf4ef032d00c61609458ddeeaf73a243670ce7fb188e20fb15b6c01c08c825d5f67547c679a1693dd04360813be3cd28c6e5a0d1dca66b410977470710a1f0b3463659be0e6d5946a4adccfae5e555a9360f44dec7b2a311ea186a6bc574fe00b89dc254481c78db835a1971ae2b22ce2caa06dee69a6b25fbef290e351a3aafc3850265ed51dc3237ea918727f9419aa4c335ba80f69a5205d277ff71b47b939780366179f7471ba6b451c21c2d4c288daa2ffc9fc4349e498c2d869021dc9214406c51ee9735d0341225efbb549f3e7b2939e90d211ebeaf5a2711926d53a32c790616502d02c483f3b357d23b958d554e478246175a12b90c2970c8ed47e9d376923812f8913cda3a6d88bd93f576cb143072c473156ae1e3925977b3b76bc804f2a5feeec49499c54463b55921e4c0d24e0bb41d
 */
.balign 32
base:
  .word 0x4e0bb41d
  .word 0x21e4c0d2
  .word 0x4463b559
  .word 0xc49499c5
  .word 0xf2a5feee
  .word 0xb76bc804
  .word 0x925977b3
  .word 0x156ae1e3
  .word 0x3072c473
  .word 0xf576cb14
  .word 0x6d88bd93
  .word 0x913cda3a
  .word 0x923812f8
  .word 0x47e9d376
  .word 0x2970c8ed
  .word 0x5a12b90c
  .word 0x47824617
  .word 0x958d554e
  .word 0xb357d23b
  .word 0x02c483f3
  .word 0x0616502d
  .word 0x53a32c79
  .word 0x2711926d
  .word 0x1ebeaf5a
  .word 0x39e90d21
  .word 0x9f3e7b29
  .word 0x25efbb54
  .word 0x35d03412
  .word 0x6c51ee97
  .word 0xdc921440
  .word 0x2d869021
  .word 0x349e498c
  .word 0x2ffc9fc4
  .word 0x4c288daa
  .word 0x51c21c2d
  .word 0x471ba6b4
  .word 0x366179f7
  .word 0x7b939780
  .word 0x77ff71b4
  .word 0x9a5205d2
  .word 0x35ba80f6
  .word 0x419aa4c3
  .word 0x918727f9
  .word 0xdc3237ea
  .word 0x0265ed51
  .word 0x3aafc385
  .word 0x290e351a
  .word 0x6b25fbef
  .word 0x06dee69a
  .word 0x22ce2caa
  .word 0x1971ae2b
  .word 0x78db835a
  .word 0xc254481c
  .word 0xfe00b89d
  .word 0x6a6bc574
  .word 0xa311ea18
  .word 0x44dec7b2
  .word 0x55a9360f
  .word 0xccfae5e5
  .word 0x5946a4ad
  .word 0x59be0e6d
  .word 0xf0b34636
  .word 0x470710a1
  .word 0x6b410977
  .word 0xa0d1dca6
  .word 0xcd28c6e5
  .word 0x60813be3
  .word 0x693dd043
  .word 0x47c679a1
  .word 0x25d5f675
  .word 0xc01c08c8
  .word 0x20fb15b6
  .word 0xe7fb188e
  .word 0xa243670c
  .word 0xddeeaf73
  .word 0x61609458
  .word 0xf032d00c
  .word 0x5d9baf4e
  .word 0xb8153b29
  .word 0xd49a7737
  .word 0x93a52e44
  .word 0xe7b3934e
  .word 0xbd385c49
  .word 0x90d8a9c0
  .word 0x1fef9ef4
  .word 0xe3f6a1ea
  .word 0x7ca56f74
  .word 0x9453478a
  .word 0xf0410b36
  .word 0xc691ac8f
  .word 0xe040c559
  .word 0x10959a01
  .word 0x84b95fc0
  .word 0x0deadefd
  .word 0xf9984491
  .word 0x77d133ac

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
.zero 384
