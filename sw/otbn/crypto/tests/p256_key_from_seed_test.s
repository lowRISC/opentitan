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
       [w20,w21] <= dmem[seed0]
       [w10,w11] <= dmem[seed1] */
  li        x2, 20
  la        x3, seed0
  bn.lid    x2++, 0(x3)
  bn.lid    x2, 32(x3)
  li        x2, 10
  la        x3, seed1
  bn.lid    x2++, 0(x3)
  bn.lid    x2, 32(x3)

  /* Generate the derived secret key. */
  jal       x1, p256_key_from_seed

  ecall

.data

/* Full test data for reference (randomly generated):
Seed shares:
0x2bac5b0bd7c77320a210c4be446984ccbb6a02057843d9a2c48e8981128c13393c174a162335f23f
0x63e2e86d4e67f1f717bcfeef551f77d199dd9f5af7d1a8736f2f939abeb67c9e2df4bec0225596d6

Expected key shares:
0xe46bcaf84b3890e19def3b61bc577b4b45c0f8b23ed867e3302b5143e9e71859e3ef3615df0ace13
0x63e2e86d4e67f1f717bcfeef551f77d199dd9f5af7d1a8736f2f939abeb67c9e2df4bec0225596d6

Real masked seed value:
0x484eb36699a082d7b5ac3a511176f31d22b79d5f8f9271d1aba11a1bac3a6fa711e3f4d6016064e9

Real masked value of key (seed mod n):
0x4f4cbd282f87bcdf35ab4783cd934744c2865e67bd8a418324fc72bdefdf454b
*/

/* First share of seed (320 bits). */
.balign 32
seed0:
  .word 0x2335f23f
  .word 0x3c174a16
  .word 0x128c1339
  .word 0xc48e8981
  .word 0x7843d9a2
  .word 0xbb6a0205
  .word 0x446984cc
  .word 0xa210c4be
  .word 0xd7c77320
  .word 0x2bac5b0b
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000

/* Second share of seed (320 bits) */
.balign 32
seed1:
  .word 0x225596d6
  .word 0x2df4bec0
  .word 0xbeb67c9e
  .word 0x6f2f939a
  .word 0xf7d1a873
  .word 0x99dd9f5a
  .word 0x551f77d1
  .word 0x17bcfeef
  .word 0x4e67f1f7
  .word 0x63e2e86d
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
