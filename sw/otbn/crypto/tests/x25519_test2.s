/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for X25519.
 *
 * Runs test vector 2 from RFC 7748, section 5.2:
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
  .word 0xd4e9664b
  .word 0x3c67b4d1
  .word 0x9126d25a
  .word 0xf56a7d95
  .word 0x21641bc1
  .word 0xd401eae0
  .word 0x9e16a42c
  .word 0x0dba1879

.balign 32
u:
  .word 0x120f21e5
  .word 0xd3116878
  .word 0x9d95b7f4
  .word 0x2cae3805
  .word 0x10e7db31
  .word 0x3e3cc06f
  .word 0x49d54cfc
  .word 0x93a415c7
