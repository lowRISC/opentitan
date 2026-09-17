/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * OTBN simulation test for masked HKDF-SHA256 (RFC 5869 Test Case 1).
 *
 * Test Vector (RFC 5869 Section A.1):
 *   Hash = SHA-256
 *   IKM  = 0x0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b (22 octets)
 *   salt = 0x000102030405060708090a0b0c (13 octets)
 *   info = 0xf0f1f2f3f4f5f6f7f8f9 (10 octets)
 *   L    = 42 octets (2 blocks of 32 bytes)
 *
 * Expected PRK:
 *   077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5
 * Expected T(1) (OKM[0..31]):
 *   3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf
 * Expected T(2) (OKM[32..63], first 10 bytes are OKM[32..41]):
 *   34007208d5b887185865b4b0a85a993b89b9b65683d60f0106d28fff039d0b6f
 */

.section .text.start
main:
  /* Run masked HKDF-SHA256 (Extract + Expand) */
  jal      x1, hkdf_sha256_masked

  /* Unmask PRK into w2 for test verification ONLY */
  la       x2, prk_s0
  li       x3, 0
  bn.lid   x3, 0(x2)
  la       x2, prk_s1
  li       x3, 1
  bn.lid   x3, 0(x2)
  bn.xor   w2, w0, w1

  /* Unmask T(1) = OKM[0..31] into w5 for test verification ONLY */
  la       x2, okm_s0
  li       x3, 3
  bn.lid   x3, 0(x2)
  la       x2, okm_s1
  li       x3, 4
  bn.lid   x3, 0(x2)
  bn.xor   w5, w3, w4

  /* Unmask T(2) = OKM[32..63] into w8 for test verification ONLY */
  la       x2, okm_s0
  li       x3, 6
  bn.lid   x3, 32(x2)
  la       x2, okm_s1
  li       x3, 7
  bn.lid   x3, 32(x2)
  bn.xor   w8, w6, w7

  ecall

.data

/* Unmasked salt (13 bytes: 0x00..0x0c, zero-padded to 64 bytes) */
.balign 32
.globl salt
salt:
  .word 0x03020100
  .word 0x07060504
  .word 0x0b0a0908
  .word 0x0000000c
  .word 0x00000000, 0x00000000, 0x00000000, 0x00000000
  .word 0x00000000, 0x00000000, 0x00000000, 0x00000000
  .word 0x00000000, 0x00000000, 0x00000000, 0x00000000

/* Boolean-shared IKM (22 bytes of 0x0b masked with arbitrary shares) */
.balign 32
.globl ikm_s0
ikm_s0:
  .word 0x0b0b0b0b ^ 0x11111111
  .word 0x0b0b0b0b ^ 0x22222222
  .word 0x0b0b0b0b ^ 0x33333333
  .word 0x0b0b0b0b ^ 0x44444444
  .word 0x0b0b0b0b ^ 0x55555555
  .word 0x00000b0b ^ 0x66666666
  .word 0x00000000 ^ 0x77777777
  .word 0x00000000 ^ 0x88888888
  .word 0x00000000 ^ 0x99999999
  .word 0x00000000 ^ 0xaaaaaaaa
  .word 0x00000000 ^ 0xbbbbbbbb
  .word 0x00000000 ^ 0xcccccccc
  .word 0x00000000 ^ 0xdddddddd
  .word 0x00000000 ^ 0xeeeeeeee
  .word 0x00000000 ^ 0xffffffff
  .word 0x00000000 ^ 0x12345678
  .zero 32

.balign 32
.globl ikm_s1
ikm_s1:
  .word 0x11111111, 0x22222222, 0x33333333, 0x44444444
  .word 0x55555555, 0x66666666, 0x77777777, 0x88888888
  .word 0x99999999, 0xaaaaaaaa, 0xbbbbbbbb, 0xcccccccc
  .word 0xdddddddd, 0xeeeeeeee, 0xffffffff, 0x12345678
  .zero 32

.balign 4
.globl ikm_len
ikm_len:
  .word 22

/* Unmasked info (10 bytes: 0xf0..0xf9) */
.balign 32
.globl info
info:
  .word 0xf3f2f1f0
  .word 0xf7f6f5f4
  .word 0x0000f9f8
  .word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
  .zero 64

.balign 4
.globl info_len
info_len:
  .word 10

/* Generate 2 blocks (64 bytes) to cover L=42 bytes */
.balign 4
.globl num_okm_blocks
num_okm_blocks:
  .word 2

.bss

.balign 32
.globl prk_s0
prk_s0:
  .zero 32

.balign 32
.globl prk_s1
prk_s1:
  .zero 32

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
  .zero 192

.balign 32
.globl msg_s1
msg_s1:
  .zero 192

.balign 32
.globl state_s0
state_s0:
  .zero 32

.balign 32
.globl state_s1
state_s1:
  .zero 32
