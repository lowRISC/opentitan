/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for bignum LCM.
 */

.section .text.start

main:
  /* Init all-zero register. */
  bn.xor  w31, w31, w31

  /* Operand limb count (2). */
  li      x30, 2

  /* dmem[result] <= lcm(dmem[x], dmem[y]) */
  la      x10, x
  la      x11, y
  la      x12, result
  jal     x1, bignum_mul

  ecall


.data

/**
 * First operand (512 bits).
 *
 * x = 0xc2b10606d4680327bf724c089eda7fdab8f34e60773ec9941fea622c716cac23e09f11b57d5680cc40a8beaf6f257cda94d10d9a9e9da73a6a7ec6eb789a24ae
 */
.balign 32
x:
  .word 0x789a24ae
  .word 0x6a7ec6eb
  .word 0x9e9da73a
  .word 0x94d10d9a
  .word 0x6f257cda
  .word 0x40a8beaf
  .word 0x7d5680cc
  .word 0xe09f11b5
  .word 0x716cac23
  .word 0x1fea622c
  .word 0x773ec994
  .word 0xb8f34e60
  .word 0x9eda7fda
  .word 0xbf724c08
  .word 0xd4680327
  .word 0xc2b10606


/**
 * Second operand (512 bits).
 *
 * y = 0xc0083ebf3a028d55b8c59df6120040041f889cf74bd388446040e2bd1f64d1c763828536f5b56350de19c3e5e27ffe80e5d71f3f3aec479dd75f140b4d9de2e0
 */
.balign 32
y:
  .word 0x4d9de2e0
  .word 0xd75f140b
  .word 0x3aec479d
  .word 0xe5d71f3f
  .word 0xe27ffe80
  .word 0xde19c3e5
  .word 0xf5b56350
  .word 0x63828536
  .word 0x1f64d1c7
  .word 0x6040e2bd
  .word 0x4bd38844
  .word 0x1f889cf7
  .word 0x12004004
  .word 0xb8c59df6
  .word 0x3a028d55
  .word 0xc0083ebf

/**
 * Result buffer (1024 bits).
 */
.balign 32
result:
  .zero 128
