/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.globl hkdf_sha256_masked
.globl hkdf_extract_sha256_masked
.globl hkdf_expand_sha256_masked

.text

/**
 * Masked HKDF-SHA256 (RFC 5869) for OTBN.
 *
 * Computes:
 *   1. HKDF-Extract(salt, IKM) -> (prk_s0, prk_s1)
 *   2. HKDF-Expand(PRK, info, L) -> (okm_s0, okm_s1)
 *
 * All secret values (IKM, PRK, intermediate HMAC states/digests, and OKM)
 * remain boolean-shared throughout execution. Share 0 and Share 1 never
 * occupy the same register or ALU datapath without clearing.
 *
 * Expected DMEM symbols provided by caller / application:
 *   - salt           (64B, aligned 32): Unmasked salt, zero-padded to 64 bytes
 *   - ikm_s0         (96B, aligned 32): Share 0 of Input Keying Material
 *   - ikm_s1         (96B, aligned 32): Share 1 of Input Keying Material
 *   - ikm_len        (4B,  aligned 4) : Byte length of IKM (0 <= ikm_len <= 96)
 *   - info           (96B, aligned 32): Unmasked context info string
 *   - info_len       (4B,  aligned 4) : Byte length of info (0 <= info_len <= 86)
 *   - num_okm_blocks (4B,  aligned 4) : Number of 32-byte OKM blocks N (1 <= N <= 8)
 *   - prk_s0         (32B, aligned 32): Output Share 0 of extracted PRK
 *   - prk_s1         (32B, aligned 32): Output Share 1 of extracted PRK
 *   - okm_s0         (256B, aligned 32): Output Share 0 of expanded OKM (32*N bytes)
 *   - okm_s1         (256B, aligned 32): Output Share 1 of expanded OKM (32*N bytes)
 *   - msg_s0         (>=192B, aligned 32): Scratch message Share 0 buffer for SHA-256
 *   - msg_s1         (>=192B, aligned 32): Scratch message Share 1 buffer for SHA-256
 *   - state_s0       (32B, aligned 32): Hash state Share 0 buffer for SHA-256
 *   - state_s1       (32B, aligned 32): Hash state Share 1 buffer for SHA-256
 */
hkdf_sha256_masked:
  jal      x1, hkdf_extract_sha256_masked
  jal      x1, hkdf_expand_sha256_masked
  ret

/**
 * Masked HKDF-Extract: PRK = HMAC-SHA256(salt, IKM).
 *
 * Reads unmasked `salt` and boolean-masked `(ikm_s0, ikm_s1)` of length
 * `ikm_len`, and writes boolean-masked 32-byte PRK to `(prk_s0, prk_s1)`.
 */
hkdf_extract_sha256_masked:
  /* Copy ikm_s0/ikm_s1 (96B = 3 WDRs) to scratch hmac_msg_s0/hmac_msg_s1 with fresh URND re-masking */
  la       x8,  ikm_s0
  la       x9,  ikm_s1
  la       x10, hmac_msg_s0
  la       x11, hmac_msg_s1
  bn.xor   w22, w22, w22
  loopi    3, 2
    jal      x1, remask_shared_wdr
    nop

  /* Inner HMAC key block: msg[0..63] = (salt ^ ipad) shared with URND */
  la       x12, ipad_const
  jal      x1, prepare_salt_key_block

  /* Run inner HMAC hash on IKM */
  la       x2, ikm_len
  lw       x14, 0(x2)
  jal      x1, hmac_sha256_inner

  /* Outer HMAC key block: msg[0..63] = (salt ^ opad) shared with URND */
  la       x12, opad_const
  jal      x1, prepare_salt_key_block

  /* Run outer HMAC hash on inner digest */
  jal      x1, hmac_sha256_outer

  /* Convert final state shares to big-endian stream bytes in prk_s0 / prk_s1 */
  la       x12, prk_s0
  la       x13, prk_s1
  jal      x0,  state_to_be_masked

/**
 * Masked HKDF-Expand: OKM = T(1) || T(2) || ... || T(N)
 * where T(i) = HMAC-SHA256(PRK, T(i-1) || info || byte(i)).
 *
 * Reads boolean-masked `(prk_s0, prk_s1)`, unmasked `info` (`info_len` bytes),
 * and `num_okm_blocks` (N), and writes boolean-masked OKM to `(okm_s0, okm_s1)`.
 */
hkdf_expand_sha256_masked:
  li       x24, 1               /* x24 <= block counter i = 1 */
  la       x2, num_okm_blocks
  lw       x25, 0(x2)           /* x25 <= total blocks N */
  la       x26, okm_s0          /* x26 <= pointer to okm_s0 block i */
  la       x27, okm_s1          /* x27 <= pointer to okm_s1 block i */

.L_expand_loop:
  /* Load info_len + 1 into x14 */
  la       x2, info_len
  lw       x14, 0(x2)
  addi     x14, x14, 1
  la       x10, hmac_msg_s0
  la       x11, hmac_msg_s1

  li       x2, 1
  beq      x24, x2, .L_expand_write_info

  /* For iterations i > 1, prepend T(i-1) (32B) to hmac_msg_s0 and hmac_msg_s1 */
  addi     x14, x14, 32
  addi     x8,  x26, -32        /* pointer to T(i-1) Share 0 */
  addi     x9,  x27, -32        /* pointer to T(i-1) Share 1 */
  bn.xor   w22, w22, w22
  jal      x1,  remask_shared_wdr

.L_expand_write_info:
  /* Zero 3 WDRs (96B) at x10, write info || byte(i), and mask into x10/x11 */
  addi     x12, x10, 0
  bn.xor   w31, w31, w31
  li       x3, 31
  bn.sid   x3, 0(x12)
  bn.sid   x3, 32(x12)
  bn.sid   x3, 64(x12)
  jal      x1, write_info_and_counter

  addi     x2,  x12, 0
  loopi    3, 2
    jal      x1, mask_unmasked_wdr
    nop
  /* Inner HMAC key block: msg[0..63] = (PRK_padded ^ ipad) */
  la       x12, ipad_const
  jal      x1, prepare_prk_key_block

  /* Run inner HMAC hash on M_i (length in x14) */
  jal      x1, hmac_sha256_inner

  /* Outer HMAC key block: msg[0..63] = (PRK_padded ^ opad) */
  la       x12, opad_const
  jal      x1, prepare_prk_key_block

  /* Run outer HMAC hash */
  jal      x1, hmac_sha256_outer

  /* Store T(i) in big-endian byte stream order to okm_s0[32*(i-1)] / okm_s1[32*(i-1)] */
  addi     x12, x26, 0
  addi     x13, x27, 0
  jal      x1, state_to_be_masked

  /* Advance pointers and loop for next block */
  addi     x26, x26, 32
  addi     x27, x27, 32
  addi     x24, x24, 1
  addi     x25, x25, -1
  bne      x25, x0, .L_expand_loop

  ret

/**
 * Prepares 64-byte masked key block from unmasked `salt` and pad constant at 0(x12).
 */
prepare_salt_key_block:
  la       x2,  salt
  la       x10, msg_s0
  la       x11, msg_s1
  li       x5,  22
  bn.lid   x5,  0(x12)
  jal      x1,  mask_unmasked_wdr_xor_w22
  jal      x0,  mask_unmasked_wdr_xor_w22

/**
 * Prepares 64-byte masked key block from masked `(prk_s0, prk_s1)` (padded with
 * 32 zero bytes) and pad constant at 0(x12).
 */
prepare_prk_key_block:
  la       x10, msg_s0
  la       x11, msg_s1
  la       x8,  prk_s0
  la       x9,  prk_s1
  li       x5,  22
  bn.lid   x5,  0(x12)
  jal      x1,  remask_shared_wdr
  addi     x2,  x12, 0
  jal      x0,  mask_unmasked_wdr

/**
 * Writes unmasked `info` (length dmem[info_len]) followed by counter byte `x24`
 * into the 32-byte zero-initialized buffer at 0(x12).
 *
 * Preserves: x12, x14, x16, x24, x25, x26, x27
 */
write_info_and_counter:
  la       x2, info_len
  lw       x15, 0(x2)
  la       x18, info
  addi     x2, x12, 0
  li       x21, 22

.L_info_word_loop:
  addi     x17, x15, -4
  srli     x17, x17, 31
  bne      x17, x0, .L_info_partial
  lw       x5, 0(x18)
  sw       x5, 0(x2)
  jal      x0, .L_info_word_next

.L_info_partial:
  srli     x17, x15, 31
  bne      x17, x0, .L_info_word_next

  /* rem == 0: no bytes from info needed, just store counter byte x24 */
  bne      x15, x0, .L_info_partial_nonzero
  sw       x24, 0(x2)
  jal      x0, .L_info_word_next

.L_info_partial_nonzero:
  lw       x5, 0(x18)

  /* rem == 1 */
  addi     x17, x15, -1
  addi     x7, x0, 0xff
  slli     x8, x24, 8
  beq      x17, x0, .L_info_store_partial

  /* rem == 2 */
  addi     x17, x15, -2
  lui      x7, 0x10
  addi     x7, x7, -1
  slli     x8, x24, 16
  beq      x17, x0, .L_info_store_partial

  /* rem == 3 */
  lui      x7, 0x1000
  addi     x7, x7, -1
  slli     x8, x24, 24

.L_info_store_partial:
  and      x5, x5, x7
  or       x5, x5, x8
  sw       x5, 0(x2)

.L_info_word_next:
  addi     x2,  x2,  4
  addi     x18, x18, 4
  addi     x15, x15, -4
  addi     x21, x21, -1
  bne      x21, x0, .L_info_word_loop
  ret

/**
 * Pads boolean-masked message in hmac_msg_s0/hmac_msg_s1 (length x14 bytes)
 * into msg_s0[64..191] / msg_s1[64..191], initializes SHA-256 state shares,
 * and runs sha256_masked.
 */
hmac_sha256_inner:
  /* Pre-fill msg_s0[64..191] and msg_s1[64..191] with fresh random zero-shares */
  la       x10, msg_s0
  addi     x10, x10, 64
  la       x11, msg_s1
  addi     x11, x11, 64
  li       x3, 11
  loopi    4, 3
    bn.wsrr  w11, URND
    bn.sid   x3, 0(x10++)
    bn.sid   x3, 0(x11++)
  bn.wsrr  w11, URND
  bn.xor   w31, w31, w31

  /* Copy valid message bytes and insert masked 0x80 byte */
  la       x10, msg_s0
  addi     x10, x10, 64
  la       x11, msg_s1
  addi     x11, x11, 64
  la       x12, hmac_msg_s0
  la       x13, hmac_msg_s1
  addi     x15, x14, 0
  li       x21, 30

.L_hmac_inner_word_loop:
  addi     x17, x15, -4
  srli     x17, x17, 31
  bne      x17, x0, .L_hmac_inner_partial
  lw       x5, 0(x12)
  sw       x5, 0(x10)
  li       x5, 0
  lw       x6, 0(x13)
  sw       x6, 0(x11)
  li       x6, 0
  jal      x0, .L_hmac_inner_word_next

.L_hmac_inner_partial:
  srli     x17, x15, 31
  bne      x17, x0, .L_hmac_inner_word_next

  /* rem == 0: no source message bytes needed, just XOR 0x80 into Share 0 */
  bne      x15, x0, .L_hmac_inner_partial_nonzero
  lw       x18, 0(x10)
  xori     x18, x18, 0x80
  sw       x18, 0(x10)
  li       x18, 0
  jal      x0, .L_hmac_inner_word_next

.L_hmac_inner_partial_nonzero:
  /* rem == 1 */
  addi     x17, x15, -1
  addi     x7, x0, 0xff
  lui      x8, 0x8
  beq      x17, x0, .L_hmac_inner_apply_pad

  /* rem == 2 */
  addi     x17, x15, -2
  lui      x7, 0x10
  addi     x7, x7, -1
  lui      x8, 0x800
  beq      x17, x0, .L_hmac_inner_apply_pad

  /* rem == 3 */
  lui      x7, 0x1000
  addi     x7, x7, -1
  lui      x8, 0x80000

.L_hmac_inner_apply_pad:
  xori     x9, x7, -1
  /* Share 0 */
  lw       x5,  0(x12)
  and      x5,  x5, x7
  lw       x18, 0(x10)
  and      x18, x18, x9
  or       x5,  x5, x18
  xor      x5,  x5, x8
  sw       x5,  0(x10)
  li       x5,  0
  li       x18, 0

  /* Share 1 */
  lw       x6,  0(x13)
  and      x6,  x6, x7
  lw       x19, 0(x11)
  and      x19, x19, x9
  or       x6,  x6, x19
  sw       x6,  0(x11)
  li       x6,  0
  li       x19, 0

.L_hmac_inner_word_next:
  addi     x10, x10, 4
  addi     x11, x11, 4
  addi     x12, x12, 4
  addi     x13, x13, 4
  addi     x15, x15, -4
  addi     x21, x21, -1
  bne      x21, x0, .L_hmac_inner_word_loop

  /* Append 64-bit big-endian bit length: total_bits = (64 + msg_len) * 8 */
  addi     x7, x14, 64
  slli     x7, x7, 3
  slli     x8, x7, 24
  srli     x9, x7, 8
  andi     x9, x9, 0xff
  slli     x9, x9, 16
  or       x8, x8, x9

  addi     x17, x14, -56
  srli     x17, x17, 31
  bne      x17, x0, .L_hmac_inner_2blocks
  li       x30, 3
  la       x10, msg_s0
  addi     x10, x10, 188
  jal      x0, .L_hmac_inner_store_len

.L_hmac_inner_2blocks:
  li       x30, 2
  la       x10, msg_s0
  addi     x10, x10, 124

.L_hmac_inner_store_len:
  lw       x5, 0(x10)
  xor      x5, x5, x8
  sw       x5, 0(x10)
  li       x5, 0

  jal      x1, sha256_init_state_masked
  la       x10, msg_s0
  la       x11, msg_s1
  jal      x0, sha256_masked

/**
 * Runs outer HMAC-SHA256 hash on inner digest in state_s0/state_s1.
 */
hmac_sha256_outer:
  la       x12, msg_s0
  addi     x12, x12, 64
  la       x13, msg_s1
  addi     x13, x13, 64
  jal      x1, state_to_be_masked

  la       x2, hmac_outer_pad
  la       x10, msg_s0
  addi     x10, x10, 96
  la       x11, msg_s1
  addi     x11, x11, 96
  jal      x1, mask_unmasked_wdr

  jal      x1, sha256_init_state_masked
  la       x10, msg_s0
  la       x11, msg_s1
  li       x30, 2
  jal      x0, sha256_masked

/**
 * Re-masks 32B shares from 0(x8++) / 0(x9++) with fresh URND and XORs w22 into Share 0,
 * storing Share 0 to 0(x10++) and Share 1 to 0(x11++).
 */
remask_shared_wdr:
  li       x3, 21
  li       x4, 11
  bn.wsrr  w11, URND
  bn.lid   x3, 0(x8++)
  bn.xor   w21, w21, w22
  bn.xor   w21, w21, w11
  bn.sid   x3, 0(x10++)
  bn.wsrr  w21, URND
  bn.xor   w31, w31, w31
  bn.lid   x3, 0(x9++)
  bn.xor   w21, w21, w11
  bn.sid   x3, 0(x11++)
  bn.wsrr  w21, URND
  bn.wsrr  w11, URND
  bn.xor   w31, w31, w31
  ret

/**
 * Loads unmasked 32B WDR from 0(x2++), XORs w22, masks with fresh URND,
 * stores Share 0 to 0(x10++) and Share 1 to 0(x11++), and wipes registers.
 */
mask_unmasked_wdr:
  bn.xor   w22, w22, w22
mask_unmasked_wdr_xor_w22:
  li       x3, 21
  li       x4, 11
  bn.lid   x3, 0(x2++)
  bn.xor   w21, w21, w22
  bn.wsrr  w11, URND
  bn.xor   w21, w21, w11
  bn.sid   x3, 0(x10++)
  bn.wsrr  w21, URND
  bn.xor   w31, w31, w31
  bn.sid   x4, 0(x11++)
  bn.wsrr  w11, URND
  bn.xor   w31, w31, w31
  ret

/**
 * Converts state_s0 and state_s1 from SHA-256 internal word order (H[7]..H[0]
 * little-endian) to big-endian stream byte order at 0(x12) and 0(x13).
 */
state_to_be_masked:
  la       x2, bswap32_mask
  li       x3, 8
  bn.lid   x3, 0(x2)

  la       x2, state_s0
  jal      x1, reverse_and_bswap_state
  bn.sid   x6, 0(x12)
  bn.wsrr  w24, URND

  la       x2, state_s1
  jal      x1, reverse_and_bswap_state
  bn.sid   x6, 0(x13)
  bn.wsrr  w24, URND
  ret

reverse_and_bswap_state:
  li       x3, 23
  li       x6, 24
  bn.lid   x3, 0(x2)
  bn.wsrr  w24, URND
  loopi    8, 2
    bn.rshi  w23, w23, w23 >> 224
    bn.rshi  w24, w23, w24 >> 32
  bn.mov   w23, w24
  jal      x0, bswap32_w23

/**
 * Initializes state_s0 and state_s1 with fresh boolean shares of SHA-256 IV.
 */
sha256_init_state_masked:
  la       x2, sha256_iv
  la       x10, state_s0
  la       x11, state_s1
  jal      x0, mask_unmasked_wdr

.data

.balign 32
sha256_iv:
  .word 0x5be0cd19, 0x1f83d9ab, 0x9b05688c, 0x510e527f
  .word 0xa54ff53a, 0x3c6ef372, 0xbb67ae85, 0x6a09e667

.balign 32
ipad_const:
  .word 0x36363636, 0x36363636, 0x36363636, 0x36363636
  .word 0x36363636, 0x36363636, 0x36363636, 0x36363636

.balign 32
opad_const:
  .word 0x5c5c5c5c, 0x5c5c5c5c, 0x5c5c5c5c, 0x5c5c5c5c
  .word 0x5c5c5c5c, 0x5c5c5c5c, 0x5c5c5c5c, 0x5c5c5c5c

/* Second 32B WDR of outer HMAC block (bytes 96..127 of 128-byte outer message):
 * Byte 96 = 0x80, Bytes 97..123 = 0x00, Bytes 124..127 = 768 bits (0x00000300 BE) */
.balign 32
hmac_outer_pad:
  .word 0x00000080, 0x00000000, 0x00000000, 0x00000000
  .word 0x00000000, 0x00000000, 0x00000000, 0x00030000

.bss

/* Scratch buffers for masked HMAC message construction (128 bytes each) */
.balign 32
hmac_msg_s0:
  .zero 128

.balign 32
hmac_msg_s1:
  .zero 128
