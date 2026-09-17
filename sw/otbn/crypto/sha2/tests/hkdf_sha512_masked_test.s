/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * OTBN simulation test for masked HKDF-SHA512 (RFC 5869 Test Case 1 inputs).
 *
 * Test Vector:
 *   Hash = SHA-512
 *   IKM  = 0x0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b (22 octets)
 *   salt = 0x000102030405060708090a0b0c (13 octets)
 *   info = 0xf0f1f2f3f4f5f6f7f8f9 (10 octets)
 *   N    = 2 blocks (128 bytes total)
 */

.section .text.start
main:
  /* Run masked HKDF-SHA512 (Extract + Expand) */
  jal      x1, hkdf_sha512_masked

  /* Unmask PRK (64B) into w2 (bytes 0..31) and w3 (bytes 32..63) */
  la       x2, prk_s0
  la       x3, prk_s1
  li       x4, 0
  li       x5, 1
  bn.lid   x4, 0(x2)
  bn.lid   x5, 0(x3)
  bn.xor   w2, w0, w1
  bn.lid   x4, 32(x2)
  bn.lid   x5, 32(x3)
  bn.xor   w3, w0, w1

  /* Unmask T(1) = OKM[0..63] into w4 (bytes 0..31) and w5 (bytes 32..63) */
  la       x2, okm_s0
  la       x3, okm_s1
  bn.lid   x4, 0(x2)
  bn.lid   x5, 0(x3)
  bn.xor   w4, w0, w1
  bn.lid   x4, 32(x2)
  bn.lid   x5, 32(x3)
  bn.xor   w5, w0, w1

  /* Unmask T(2) = OKM[64..127] into w6 (bytes 64..95) and w7 (bytes 96..127) */
  bn.lid   x4, 64(x2)
  bn.lid   x5, 64(x3)
  bn.xor   w6, w0, w1
  bn.lid   x4, 96(x2)
  bn.lid   x5, 96(x3)
  bn.xor   w7, w0, w1

  ecall

.data

/* Unmasked salt (13 bytes: 0x00..0x0c, zero-padded to 128 bytes) */
.balign 32
.globl salt
salt:
  .word 0x03020100, 0x07060504, 0x0b0a0908, 0x0000000c
  .word 0x00000000, 0x00000000, 0x00000000, 0x00000000
  .word 0x00000000, 0x00000000, 0x00000000, 0x00000000
  .word 0x00000000, 0x00000000, 0x00000000, 0x00000000
  .word 0x00000000, 0x00000000, 0x00000000, 0x00000000
  .word 0x00000000, 0x00000000, 0x00000000, 0x00000000
  .word 0x00000000, 0x00000000, 0x00000000, 0x00000000
  .word 0x00000000, 0x00000000, 0x00000000, 0x00000000

/* Boolean-shared IKM (22 bytes of 0x0b masked with arbitrary shares, 128B buffer) */
.balign 32
.globl ikm_s0
ikm_s0:
  .word 0x0b0b0b0b ^ 0x11111111, 0x0b0b0b0b ^ 0x22222222
  .word 0x0b0b0b0b ^ 0x33333333, 0x0b0b0b0b ^ 0x44444444
  .word 0x0b0b0b0b ^ 0x55555555, 0x00000b0b ^ 0x66666666
  .word 0x00000000 ^ 0x77777777, 0x00000000 ^ 0x88888888
  .word 0x00000000 ^ 0x99999999, 0x00000000 ^ 0xaaaaaaaa
  .word 0x00000000 ^ 0xbbbbbbbb, 0x00000000 ^ 0xcccccccc
  .word 0x00000000 ^ 0xdddddddd, 0x00000000 ^ 0xeeeeeeee
  .word 0x00000000 ^ 0xffffffff, 0x00000000 ^ 0x12345678
  .word 0x00000000 ^ 0x11111111, 0x00000000 ^ 0x22222222
  .word 0x00000000 ^ 0x33333333, 0x00000000 ^ 0x44444444
  .word 0x00000000 ^ 0x55555555, 0x00000000 ^ 0x66666666
  .word 0x00000000 ^ 0x77777777, 0x00000000 ^ 0x88888888
  .word 0x00000000 ^ 0x99999999, 0x00000000 ^ 0xaaaaaaaa
  .word 0x00000000 ^ 0xbbbbbbbb, 0x00000000 ^ 0xcccccccc
  .word 0x00000000 ^ 0xdddddddd, 0x00000000 ^ 0xeeeeeeee
  .word 0x00000000 ^ 0xffffffff, 0x00000000 ^ 0x12345678

.balign 32
.globl ikm_s1
ikm_s1:
  .word 0x11111111, 0x22222222, 0x33333333, 0x44444444
  .word 0x55555555, 0x66666666, 0x77777777, 0x88888888
  .word 0x99999999, 0xaaaaaaaa, 0xbbbbbbbb, 0xcccccccc
  .word 0xdddddddd, 0xeeeeeeee, 0xffffffff, 0x12345678
  .word 0x11111111, 0x22222222, 0x33333333, 0x44444444
  .word 0x55555555, 0x66666666, 0x77777777, 0x88888888
  .word 0x99999999, 0xaaaaaaaa, 0xbbbbbbbb, 0xcccccccc
  .word 0xdddddddd, 0xeeeeeeee, 0xffffffff, 0x12345678

.balign 4
.globl ikm_len
ikm_len:
  .word 22

/* Unmasked info (10 bytes: 0xf0..0xf9) */
.balign 32
.globl info
info:
  .word 0xf3f2f1f0, 0xf7f6f5f4, 0x0000f9f8, 0x00000000
  .word 0x00000000, 0x00000000, 0x00000000, 0x00000000
  .zero 64

.balign 4
.globl info_len
info_len:
  .word 10

/* Generate 2 blocks (128 bytes) */
.balign 4
.globl num_okm_blocks
num_okm_blocks:
  .word 2

.bss

.balign 32
.globl prk_s0
prk_s0:
  .zero 64

.balign 32
.globl prk_s1
prk_s1:
  .zero 64

.balign 32
.globl okm_s0
okm_s0:
  .zero 256

.balign 32
.globl okm_s1
okm_s1:
  .zero 256

.balign 32
.globl msg_s0
msg_s0:
  .zero 384

.balign 32
.globl msg_s1
msg_s1:
  .zero 384

.balign 32
.globl state_s0
state_s0:
  .zero 64

.balign 32
.globl state_s1
state_s1:
  .zero 64
