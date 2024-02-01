/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for OTBN bignum division.
 */

.section .text.start

main:
  /* Init all-zero register. */
  bn.xor    w31, w31, w31

  /* Load the number of limbs for this test. */
  li        x30, 8

  /* Load DMEM pointers. */
  la        x10, numerator
  la        x11, denominator
  la        x12, quotient

  /* Compute the result.
       dmem[quotient] <= dmem[numerator] // dmem[denominator]
       dmem[remainder] <= dmem[numerator] % dmem[denominator] */
  jal       x1, div

  /* Read the quotient and remainder into registers for the test framework to
     check.
       [w0..w7] <= dmem[quotient] = quotient
       [w10..w17] <= dmem[numerator] = remainder */
  li        x2, 0
  li        x3, 10
  loop      x30, 4
    bn.lid    x2, 0(x12++)
    addi      x2, x2, 1
    bn.lid    x3, 0(x10++)
    addi      x3, x3, 1

  ecall

.data

/*
Numerator: randomly-generated number in the range [0,2^2048)

x[0] = 0x30a71e74d58458c5f4f568619d950fc5db1abd2efab55d781ab04c367e3db787
x[1] = 0x92ba9175cffc2490c49aa037b4a59117e0b39b798ddd198326381243ec2660e8
x[2] = 0x012c5df6a4ffdb3e950e816c8776d53103f191cc52c15e20f8ca09e4b13cde15
x[3] = 0x661e039e90c201f97af7af1a0789b983283458499355374a84061ef01079cc8e
x[4] = 0x6cade39974deeef59bf6170dc36c3967bcc0923baf567f20957fbfa6307aaa32
x[5] = 0xb6d5e746d74c093c0b3ad6627ba4486fb071d294446c18136ce5fd2f9d435e5b
x[6] = 0x9e615411f31126f11b50b53a6affc70a85904af07c9ec2c93e7ee3676b7e6bd8
x[7] = 0x17dd24c9edce535e0f887348c49d4b34d6135287398af62fdaa5fee802cfb328
*/
.balign 32
numerator:
  .word 0x7e3db787
  .word 0x1ab04c36
  .word 0xfab55d78
  .word 0xdb1abd2e
  .word 0x9d950fc5
  .word 0xf4f56861
  .word 0xd58458c5
  .word 0x30a71e74
  .word 0xec2660e8
  .word 0x26381243
  .word 0x8ddd1983
  .word 0xe0b39b79
  .word 0xb4a59117
  .word 0xc49aa037
  .word 0xcffc2490
  .word 0x92ba9175
  .word 0xb13cde15
  .word 0xf8ca09e4
  .word 0x52c15e20
  .word 0x03f191cc
  .word 0x8776d531
  .word 0x950e816c
  .word 0xa4ffdb3e
  .word 0x012c5df6
  .word 0x1079cc8e
  .word 0x84061ef0
  .word 0x9355374a
  .word 0x28345849
  .word 0x0789b983
  .word 0x7af7af1a
  .word 0x90c201f9
  .word 0x661e039e
  .word 0x307aaa32
  .word 0x957fbfa6
  .word 0xaf567f20
  .word 0xbcc0923b
  .word 0xc36c3967
  .word 0x9bf6170d
  .word 0x74deeef5
  .word 0x6cade399
  .word 0x9d435e5b
  .word 0x6ce5fd2f
  .word 0x446c1813
  .word 0xb071d294
  .word 0x7ba4486f
  .word 0x0b3ad662
  .word 0xd74c093c
  .word 0xb6d5e746
  .word 0x6b7e6bd8
  .word 0x3e7ee367
  .word 0x7c9ec2c9
  .word 0x85904af0
  .word 0x6affc70a
  .word 0x1b50b53a
  .word 0xf31126f1
  .word 0x9e615411
  .word 0x02cfb328
  .word 0xdaa5fee8
  .word 0x398af62f
  .word 0xd6135287
  .word 0xc49d4b34
  .word 0x0f887348
  .word 0xedce535e
  .word 0x17dd24c9


/*
Denominator: randomly-generated number in the range [0,2^1029)

y[0] = 0xa93f588174bccf01b87ec77011245a532cf05dce8a76e0288c56022f83f33037
y[1] = 0x6462378874d4e70c744356bb4456252f3ec6d42173617fcfc979d7acba068db4
y[2] = 0xd1bbe91f1e59f624a3c63cc125ad42a70d74282a0f9a3942054e7dd3a0717841
y[3] = 0x3542ac6ce4f69a9f03ffb05a17de6359c8bbbb10a2a6bef06f8a6452ec64100b
y[4] = 0x000000000000000000000000000000000000000000000000000000000000001d
y[5] = 0x0000000000000000000000000000000000000000000000000000000000000000
y[6] = 0x0000000000000000000000000000000000000000000000000000000000000000
y[7] = 0x0000000000000000000000000000000000000000000000000000000000000000
*/
.balign 32
denominator:
  .word 0x83f33037
  .word 0x8c56022f
  .word 0x8a76e028
  .word 0x2cf05dce
  .word 0x11245a53
  .word 0xb87ec770
  .word 0x74bccf01
  .word 0xa93f5881
  .word 0xba068db4
  .word 0xc979d7ac
  .word 0x73617fcf
  .word 0x3ec6d421
  .word 0x4456252f
  .word 0x744356bb
  .word 0x74d4e70c
  .word 0x64623788
  .word 0xa0717841
  .word 0x054e7dd3
  .word 0x0f9a3942
  .word 0x0d74282a
  .word 0x25ad42a7
  .word 0xa3c63cc1
  .word 0x1e59f624
  .word 0xd1bbe91f
  .word 0xec64100b
  .word 0x6f8a6452
  .word 0xa2a6bef0
  .word 0xc8bbbb10
  .word 0x17de6359
  .word 0x03ffb05a
  .word 0xe4f69a9f
  .word 0x3542ac6c
  .word 0x0000001d
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

/* Buffer for quotient. */
.balign 32
quotient:
.zero 256
