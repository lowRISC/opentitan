/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for a subcomponent of the Miller-Rabin primality test.
 *
 * Testing the test_witness subroutine in isolation can be helpful for
 * debugging and quick feedback.
 */

.section .text.start

main:
  /* Initialize all-zero register. */
  bn.xor    w31, w31, w31

  /* Set number of limbs (n=2).
       x30 <= n
       x31 <= n - 1 */
  li        x30, 2
  li        x31, 1

  /* Test the witness.
       w21 <= all 1s if dmem[input] is possibly prime, otherwise 0 */
  la         x14, witness
  la         x15, tmp
  la         x16, input
  la         x17, mont_m0inv
  la         x18, mont_rr
  jal        x1, test_witness

  ecall

.data

/* Candidate prime (composite, randomly generated) =
0xf7b5cc32e3c7c3ff6f220312fe4be4af76c9e51e8c17648c863751d70359bab17c1d7b4844e01d1ec0cd695ff3bae05dc51d95a001ab7b69f66d0c056c2dec3b
*/
.balign 32
input:
.word 0x6c2dec39
.word 0xf66d0c05
.word 0x01ab7b69
.word 0xc51d95a0
.word 0xf3bae05d
.word 0xc0cd695f
.word 0x44e01d1e
.word 0x7c1d7b48
.word 0x0359bab1
.word 0x863751d7
.word 0x8c17648c
.word 0x76c9e51e
.word 0xfe4be4af
.word 0x6f220312
.word 0xe3c7c3ff
.word 0xf7b5cc32

/* Random witness for testing. */
.balign 32
witness:
.word 0x4080769c
.word 0x1262ef4d
.word 0x98b11168
.word 0xd0f601d0
.word 0x4387fc64
.word 0x8ab79fd2
.word 0xf7252c67
.word 0xe8a0ed3c
.word 0x72a5ce33
.word 0x082fb7fd
.word 0x9d7863bb
.word 0x80ea393b
.word 0x4e4e9575
.word 0x09455e2a
.word 0x81a24e55
.word 0x256943a7

/* Precomputed Montgomery constant m0' (256 bits). */
.balign 32
mont_m0inv:
.word 0xbb5df30d
.word 0xf47b30a4
.word 0x45c4b2af
.word 0xb6e86212
.word 0xacafa4f9
.word 0x6e5afd69
.word 0x9ae7984c
.word 0xce44dadc

/* Precomputed Montgomery constant RR (512 bits). */
.balign 32
mont_rr:
.word 0xc1e31e17
.word 0x6f9be028
.word 0xcd184ada
.word 0xbbd4bbb9
.word 0x10d84741
.word 0xa11300bd
.word 0x4e5c6583
.word 0x50805ac8
.word 0x78f6cf41
.word 0x163b312e
.word 0x126593d5
.word 0x03cc62ac
.word 0x23cbc231
.word 0xa53b2634
.word 0x5d9d6071
.word 0xdf10ee86

.section .scratchpad

/* Temporary working buffer (512 bits). */
.balign 32
tmp:
.zero 64
