/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for P256 secret key derivation.
 */

.section .text.start

key_from_seed_test:
  /* Init all-zero register. */
  bn.xor    w31, w31, w31

  /* Load shares of seed from DMEM.
       [w21,w20] <= dmem[seed0]
       [w23,w33] <= dmem[seed1] */
  li        x2, 20
  la        x3, seed0
  bn.lid    x2, 0(x3++)
  li        x2, 21
  bn.lid    x2++, 0(x3)
  la        x3, seed1
  bn.lid    x2, 0(x3++)
  li        x2, 23
  bn.lid    x2, 0(x3)

  /* Generate the derived secret key. */
  jal       x1, p256_key_from_seed

  ecall

.data

/* Full test data for reference (randomly generated):

Seed shares:
0xa504e1c1c414883cea0f5e27cfba94f1cb4a21734c7af8085e561a3856f7bdde1e9a829fab5b7010
0x2f2876129e3e835654cd40e4208329529bb79deec3927359daf2e50762a8c404debb1d2488dafa5c

Expected key shares:
0x5b0421c0bbeb881469f4dddfceb69450b5461eaecc5617f7a9b21a37d1b6b5d5e16682969aa68ff0
0x2f2876129e3e835654cd40e4208329529bb79deec3927359daf2e50762a8c404debb1d2488dafa5c

Real seed value:
0x8a2c97d35a2a0b6abec21ec3ef39bda350fdbc9d8fe88b5184a4ff3f345f79dac0219fbb23818a4c

Real masked value of key (seed mod n):
0x18ec2a2e0ae31a657534e99429990b0d42bc6e1b9ab120bc1218be813585edae
*/

/* First share of seed (320 bits). */
.balign 32
seed0:
  .word 0xab5b7010
  .word 0x1e9a829f
  .word 0x56f7bdde
  .word 0x5e561a38
  .word 0x4c7af808
  .word 0xcb4a2173
  .word 0xcfba94f1
  .word 0xea0f5e27
  .word 0xc414883c
  .word 0xa504e1c1
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000

/* Second share of seed (320 bits) */
.balign 32
seed1:
  .word 0x88dafa5c
  .word 0xdebb1d24
  .word 0x62a8c404
  .word 0xdaf2e507
  .word 0xc3927359
  .word 0x9bb79dee
  .word 0x20832952
  .word 0x54cd40e4
  .word 0x9e3e8356
  .word 0x2f287612
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
