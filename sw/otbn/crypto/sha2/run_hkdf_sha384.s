/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.section .text.start
main:
  /* Run masked HKDF-SHA384 (Extract + Expand) */
  jal      x1, hkdf_sha384_masked

  ecall

.bss

/* Unmasked salt, zero-padded to 128 bytes */
.balign 32
.globl salt
salt:
.zero 128

/* Input Keying Material (IKM) boolean shares (up to 111 bytes) */
.balign 32
.globl ikm_s0
ikm_s0:
.zero 128

.balign 32
.globl ikm_s1
ikm_s1:
.zero 128

/* Unmasked context/application info string (up to 86 bytes) */
.balign 32
.globl info
info:
.zero 96

/* Extracted Pseudorandom Key (PRK) boolean shares (48 bytes + 16 zero bytes each) */
.balign 32
.globl prk_s0
prk_s0:
.zero 64

.balign 32
.globl prk_s1
prk_s1:
.zero 64

/* Expanded Output Keying Material (OKM) boolean shares (up to 6 blocks = 288 bytes each) */
.balign 32
.globl okm_s0
okm_s0:
.zero 288

.balign 32
.globl okm_s1
okm_s1:
.zero 288

/* Scratch message buffers for SHA-384 (3 blocks = 384 bytes each) */
.balign 32
.globl msg_s0
msg_s0:
.zero 384

.balign 32
.globl msg_s1
msg_s1:
.zero 384

/* Hash state shares for SHA-384 (64 bytes each) */
.balign 32
.globl state_s0
state_s0:
.zero 64

.balign 32
.globl state_s1
state_s1:
.zero 64

/* Byte length of IKM (0 <= ikm_len <= 111) */
.balign 4
.globl ikm_len
ikm_len:
.zero 4

/* Byte length of info (0 <= info_len <= 30) */
.balign 4
.globl info_len
info_len:
.zero 4

/* Number of 48-byte output blocks N to generate (1 <= N <= 5) */
.balign 4
.globl num_okm_blocks
num_okm_blocks:
.zero 4
