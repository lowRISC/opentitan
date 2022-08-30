/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * This application runs X25519 with a sideloaded secret key.
 *
 * Computes X25519(k, u) according to RFC 7748, where:
 *   - k is the 256-bit value derived from the sideloaded key
 *   - u is the caller-provided Montgomery u-coordinate.
 *
 * The key manager provides 384 bits of sideloaded data, expressed in 2 shares
 * across the special registers KEY_S0_L, KEY_S0_H, KEY_S1_L, and KEY_S1_H.
 * Since we only need 256 bits, the extra bits in KEY_S0_H and KEY_S1_H are
 * ignored and the encoded value of k, enc(k), is equal to KEY_S0_L ^ KEY_S1_L.
 *
 * The caller must check that the key manager has finished generating the key
 * before attempting to run this application.
 */

.section .text.start

main:
  /* w7 <= KEY_S0_L */
  bn.wsrr w7, 4
  /* w8 <= KEY_S1_L */
  bn.wsrr w8, 6
  /* w8 <= KEY_S0_L ^ KEY_S1_L = enc(k) */
  bn.xor  w8, w7, w8

  /* w9 <= dmem[enc_u] = enc(u) */
  li      x2, 9
  la      x3, enc_u
  bn.lid  x2, 0(x3)

  /* w22 <= enc(X25519(k, u)) */
  jal     x1, X25519

  /* dmem[enc_result] <= w22 = enc(X25519(k, u)) */
  li      x2, 22
  la      x3, enc_result
  bn.sid  x2, 0(x3)

  ecall

.data

/* Input Montgomery u-coordinate (encoded, 256 bits). */
.globl enc_u
.balign 32
enc_u:
.zero 32

/* Output Montgomery u-coordinate (encoded, 256 bits). */
.globl enc_result
.balign 32
enc_result:
.zero 32
