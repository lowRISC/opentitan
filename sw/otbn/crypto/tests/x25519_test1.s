/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for X25519.
 *
 * Runs test vector 1 from RFC 7748, section 5.2:
 *   https://datatracker.ietf.org/doc/html/rfc7748#section-5.2
 */

.section .text.start

main:
  /* w8 <= dmem[k] = enc(k) */
  li      x2, 8
  la      x3, k
  bn.lid  x2, 0(x3)

  /* w9 <= dmem[u] = enc(u) */
  li      x2, 9
  la      x3, u
  bn.lid  x2, 0(x3)

  /* w22 <= X25519(k, u) */
  jal     x1, X25519

  ecall

.data

.balign 32
k:
  .word 0x6be346a5
  .word 0x9d7c52f0
  .word 0x4b15163b
  .word 0xdd5e4682
  .word 0x0a4c1462
  .word 0x185afcc1
  .word 0x44226a50
  .word 0xc49a44ba

.balign 32
u:
  .word 0x6768dbe6
  .word 0xdb303058
  .word 0xa4c19435
  .word 0x7c5fb124
  .word 0xec246672
  .word 0x3b35b326
  .word 0xa603a910
  .word 0x4c1cabd0
