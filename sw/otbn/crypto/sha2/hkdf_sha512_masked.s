/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.globl hkdf_sha512_masked
.globl hkdf_extract_sha512_masked
.globl hkdf_expand_sha512_masked

.text

/**
 * Masked HKDF-SHA512 (RFC 5869) for OTBN.
 *
 * Computes:
 *   1. HKDF-Extract(salt, IKM) -> (prk_s0, prk_s1)   [64 bytes]
 *   2. HKDF-Expand(PRK, info, L) -> (okm_s0, okm_s1) [64*N bytes]
 *
 * All secret values (IKM, PRK, intermediate HMAC states/digests, and OKM)
 * remain boolean-shared throughout execution. Share 0 and Share 1 never
 * occupy the same register or ALU datapath without clearing.
 *
 * Expected DMEM symbols provided by caller / application:
 *   - salt           (128B, aligned 32): Unmasked salt, zero-padded to 128 bytes
 *   - ikm_s0         (128B, aligned 32): Share 0 of Input Keying Material
 *   - ikm_s1         (128B, aligned 32): Share 1 of Input Keying Material
 *   - ikm_len        (4B,   aligned 4) : Byte length of IKM (0 <= ikm_len <= 111)
 *   - info           (96B,  aligned 32): Unmasked context info string
 *   - info_len       (4B,   aligned 4) : Byte length of info (0 <= info_len <= 86)
 *   - num_okm_blocks (4B,   aligned 4) : Number of 64-byte OKM blocks N (1 <= N <= 4)
 *   - prk_s0         (64B,  aligned 32): Output Share 0 of extracted PRK
 *   - prk_s1         (64B,  aligned 32): Output Share 1 of extracted PRK
 *   - okm_s0         (256B, aligned 32): Output Share 0 of expanded OKM (64*N bytes)
 *   - okm_s1         (256B, aligned 32): Output Share 1 of expanded OKM (64*N bytes)
 *   - msg_s0         (>=384B, aligned 32): Scratch message Share 0 buffer for SHA-512
 *   - msg_s1         (>=384B, aligned 32): Scratch message Share 1 buffer for SHA-512
 *   - state_s0       (64B,  aligned 32): Hash state Share 0 buffer for SHA-512
 *   - state_s1       (64B,  aligned 32): Hash state Share 1 buffer for SHA-512
 */
hkdf_sha512_masked:
  jal      x1, hkdf_extract_sha512_masked
  jal      x0, hkdf_expand_sha512_masked

/**
 * Masked HKDF-Extract: PRK = HMAC-SHA512(salt, IKM).
 */
hkdf_extract_sha512_masked:
  /* Copy ikm_s0/ikm_s1 (128B = 4 WDRs) to hmac_msg_s0/hmac_msg_s1 with fresh URND re-masking */
  la       x8,  ikm_s0
  la       x9,  ikm_s1
  la       x10, hmac_msg_s0
  la       x11, hmac_msg_s1
  bn.xor   w22, w22, w22
  loopi    4, 2
    jal      x1, remask_shared_wdr_512
    nop

  /* Inner HMAC key block: msg[0..127] = (salt ^ ipad) shared with URND */
  la       x12, ipad_const
  jal      x1, prepare_salt_key_block_512

  /* Run inner HMAC hash on IKM */
  la       x2, ikm_len
  lw       x14, 0(x2)
  jal      x1, hmac_sha512_inner

  /* Outer HMAC key block: msg[0..127] = (salt ^ opad) shared with URND */
  la       x12, opad_const
  jal      x1, prepare_salt_key_block_512

  /* Run outer HMAC hash on inner digest */
  jal      x1, hmac_sha512_outer

  /* Convert final state shares to big-endian stream bytes in prk_s0 / prk_s1 */
  la       x12, prk_s0
  la       x13, prk_s1
  jal      x0, state_to_be_masked_sha512

/**
 * Masked HKDF-Expand: OKM = T(1) || T(2) || ... || T(N)
 * where T(i) = HMAC-SHA512(PRK, T(i-1) || info || byte(i)).
 */
hkdf_expand_sha512_masked:
  li       x24, 1               /* x24 <= block counter i = 1 */
  la       x2, num_okm_blocks
  lw       x25, 0(x2)           /* x25 <= remaining blocks count */
  la       x26, okm_s0          /* x26 <= pointer to okm_s0 block i */
  la       x27, okm_s1          /* x27 <= pointer to okm_s1 block i */

.L_expand512_loop:
  la       x2, info_len
  lw       x14, 0(x2)
  addi     x14, x14, 1
  la       x10, hmac_msg_s0
  la       x11, hmac_msg_s1

  li       x2, 1
  beq      x24, x2, .L_expand512_write_info

  /* For iterations i > 1, prepend T(i-1) (64B) to hmac_msg_s0 and hmac_msg_s1 */
  addi     x14, x14, 64
  addi     x8,  x26, -64
  addi     x9,  x27, -64
  bn.xor   w22, w22, w22
  jal      x1, remask_shared_wdr_512
  jal      x1, remask_shared_wdr_512

.L_expand512_write_info:
  /* Zero 3 WDRs (96B) at x10, write info || byte(i), and mask into x10/x11 */
  addi     x12, x10, 0
  bn.xor   w31, w31, w31
  li       x3, 31
  bn.sid   x3, 0(x12)
  bn.sid   x3, 32(x12)
  bn.sid   x3, 64(x12)
  jal      x1, write_info_and_counter_512

  addi     x2, x12, 0
  loopi    3, 2
    jal      x1, mask_unmasked_wdr_512
    nop
  /* Inner HMAC key block: msg[0..127] = (PRK_padded ^ ipad) */
  la       x12, ipad_const
  jal      x1, prepare_prk_key_block_512

  /* Run inner HMAC hash on M_i (length in x14) */
  jal      x1, hmac_sha512_inner

  /* Outer HMAC key block: msg[0..127] = (PRK_padded ^ opad) */
  la       x12, opad_const
  jal      x1, prepare_prk_key_block_512

  /* Run outer HMAC hash */
  jal      x1, hmac_sha512_outer

  /* Store T(i) (64B) in big-endian byte stream order directly to okm_s0 / okm_s1 */
  addi     x12, x26, 0
  addi     x13, x27, 0
  jal      x1, state_to_be_masked_sha512
  addi     x26, x26, 64
  addi     x27, x27, 64

  /* Loop for next block */
  addi     x24, x24, 1
  addi     x25, x25, -1
  bne      x25, x0, .L_expand512_loop

  ret

/**
 * Re-masks 32B shares from 0(x8++) / 0(x9++) with fresh URND and XORs w22 into Share 0,
 * storing Share 0 to 0(x10++) and Share 1 to 0(x11++).
 */
remask_shared_wdr_512:
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
 * Helper: Loads 1 unmasked WDR from 0(x2++), XORs w22, masks with fresh URND,
 * and writes Share 0 to 0(x10++) and Share 1 to 0(x11++).
 */
mask_unmasked_wdr_512:
  bn.xor   w22, w22, w22
mask_unmasked_wdr_xor_w22_512:
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
 * Prepares 128-byte masked key block from unmasked `salt` (4 WDRs) and pad at 0(x12).
 */
prepare_salt_key_block_512:
  la       x2, salt
  la       x10, msg_s0
  la       x11, msg_s1
  li       x5, 22
  bn.lid   x5, 0(x12)
  loopi    4, 2
    jal      x1, mask_unmasked_wdr_xor_w22_512
    nop
  bn.wsrr  w22, URND
  bn.xor   w31, w31, w31
  ret

/**
 * Prepares 128-byte masked key block from masked 64-byte `(prk_s0, prk_s1)`
 * (padded with 64 zero bytes) and pad constant at 0(x12).
 */
prepare_prk_key_block_512:
  la       x8,  prk_s0
  la       x9,  prk_s1
  la       x10, msg_s0
  la       x11, msg_s1
  li       x5, 22
  bn.lid   x5, 0(x12)
  /* WDR 0 & WDR 1 (bytes 0..63): PRK ^ pad */
  jal      x1, remask_shared_wdr_512
  jal      x1, remask_shared_wdr_512
  /* WDR 2 & WDR 3 (bytes 64..127): 0 ^ pad = pad */
  addi     x2, x12, 0
  jal      x1, mask_unmasked_wdr_512
  addi     x2, x12, 0
  jal      x0, mask_unmasked_wdr_512

/**
 * Writes unmasked `info` (length dmem[info_len]) followed by counter byte `x24`
 * into zero-initialized buffer starting at 0(x12).
 *
 * Preserves: x12, x14, x16, x24, x25, x26, x27
 */
write_info_and_counter_512:
  la       x2, info_len
  lw       x15, 0(x2)
  la       x18, info
  addi     x2, x12, 0
  li       x21, 22

.L_info512_word_loop:
  addi     x17, x15, -4
  srli     x17, x17, 31
  bne      x17, x0, .L_info512_partial
  lw       x5, 0(x18)
  sw       x5, 0(x2)
  jal      x0, .L_info512_word_next

.L_info512_partial:
  srli     x17, x15, 31
  bne      x17, x0, .L_info512_word_next

  bne      x15, x0, .L_info512_partial_nonzero
  sw       x24, 0(x2)
  jal      x0, .L_info512_word_next

.L_info512_partial_nonzero:
  lw       x5, 0(x18)

  addi     x17, x15, -1
  addi     x7, x0, 0xff
  slli     x8, x24, 8
  beq      x17, x0, .L_info512_store_partial

  addi     x17, x15, -2
  lui      x7, 0x10
  addi     x7, x7, -1
  slli     x8, x24, 16
  beq      x17, x0, .L_info512_store_partial

  lui      x7, 0x1000
  addi     x7, x7, -1
  slli     x8, x24, 24

.L_info512_store_partial:
  and      x5, x5, x7
  or       x5, x5, x8
  sw       x5, 0(x2)

.L_info512_word_next:
  addi     x2,  x2,  4
  addi     x18, x18, 4
  addi     x15, x15, -4
  addi     x21, x21, -1
  bne      x21, x0, .L_info512_word_loop
  ret

/**
 * Pads boolean-masked message in hmac_msg_s0/hmac_msg_s1 (length x14 bytes)
 * into msg_s0[128..383] / msg_s1[128..383], initializes SHA-512 state shares,
 * and tail-calls sha512_masked for 2 or 3 blocks.
 */
hmac_sha512_inner:
  /* Pre-fill msg_s0[128..383] and msg_s1[128..383] (8 WDRs) with fresh random zero-shares */
  la       x10, msg_s0
  addi     x10, x10, 128
  la       x11, msg_s1
  addi     x11, x11, 128
  li       x3, 11
  loopi    8, 3
    bn.wsrr  w11, URND
    bn.sid   x3, 0(x10++)
    bn.sid   x3, 0(x11++)
  bn.wsrr  w11, URND
  bn.xor   w31, w31, w31

  /* Copy valid message bytes and insert masked 0x80 byte */
  la       x10, msg_s0
  addi     x10, x10, 128
  la       x11, msg_s1
  addi     x11, x11, 128
  la       x12, hmac_msg_s0
  la       x13, hmac_msg_s1
  addi     x15, x14, 0
  li       x21, 38

.L_hmac512_inner_word_loop:
  addi     x17, x15, -4
  srli     x17, x17, 31
  bne      x17, x0, .L_hmac512_inner_partial
  lw       x5, 0(x12)
  sw       x5, 0(x10)
  li       x5, 0
  lw       x6, 0(x13)
  sw       x6, 0(x11)
  li       x6, 0
  jal      x0, .L_hmac512_inner_word_next

.L_hmac512_inner_partial:
  srli     x17, x15, 31
  bne      x17, x0, .L_hmac512_inner_word_next

  bne      x15, x0, .L_hmac512_inner_partial_nonzero
  lw       x18, 0(x10)
  xori     x18, x18, 0x80
  sw       x18, 0(x10)
  li       x18, 0
  jal      x0, .L_hmac512_inner_word_next

.L_hmac512_inner_partial_nonzero:
  addi     x17, x15, -1
  addi     x7, x0, 0xff
  lui      x8, 0x8
  beq      x17, x0, .L_hmac512_inner_apply_pad

  addi     x17, x15, -2
  lui      x7, 0x10
  addi     x7, x7, -1
  lui      x8, 0x800
  beq      x17, x0, .L_hmac512_inner_apply_pad

  lui      x7, 0x1000
  addi     x7, x7, -1
  lui      x8, 0x80000

.L_hmac512_inner_apply_pad:
  xori     x9, x7, -1
  lw       x5,  0(x12)
  and      x5,  x5, x7
  lw       x18, 0(x10)
  and      x18, x18, x9
  or       x5,  x5, x18
  xor      x5,  x5, x8
  sw       x5,  0(x10)
  li       x5,  0
  li       x18, 0

  lw       x6,  0(x13)
  and      x6,  x6, x7
  lw       x19, 0(x11)
  and      x19, x19, x9
  or       x6,  x6, x19
  sw       x6,  0(x11)
  li       x6,  0
  li       x19, 0

.L_hmac512_inner_word_next:
  addi     x10, x10, 4
  addi     x11, x11, 4
  addi     x12, x12, 4
  addi     x13, x13, 4
  addi     x15, x15, -4
  addi     x21, x21, -1
  bne      x21, x0, .L_hmac512_inner_word_loop

  /* Append big-endian bit length: total_bits = (128 + msg_len) * 8 */
  addi     x7, x14, 128
  slli     x7, x7, 3
  slli     x8, x7, 24
  srli     x9, x7, 8
  andi     x9, x9, 0xff
  slli     x9, x9, 16
  or       x8, x8, x9

  addi     x17, x14, -112
  srli     x17, x17, 31
  bne      x17, x0, .L_hmac512_inner_2blocks
  li       x30, 3
  la       x10, msg_s0
  addi     x10, x10, 380
  jal      x0, .L_hmac512_inner_store_len

.L_hmac512_inner_2blocks:
  li       x30, 2
  la       x10, msg_s0
  addi     x10, x10, 252

.L_hmac512_inner_store_len:
  lw       x5, 0(x10)
  xor      x5, x5, x8
  sw       x5, 0(x10)
  li       x5, 0

  jal      x1, sha512_init_state_masked
  la       x10, msg_s0
  la       x11, msg_s1
  jal      x0, sha512_masked

/**
 * Runs outer HMAC-SHA512 hash on 64-byte inner digest in state_s0/state_s1.
 */
hmac_sha512_outer:
  /* Convert 64B inner digest to msg_s0+128 / msg_s1+128 (WDR 0 & WDR 1 of Block 1) */
  la       x12, msg_s0
  addi     x12, x12, 128
  la       x13, msg_s1
  addi     x13, x13, 128
  jal      x1, state_to_be_masked_sha512

  /* Write WDR 2 (offset 192: 0x80...) and WDR 3 (offset 224: length = 1536 bits = 0x0600) */
  la       x2,  hmac512_outer_pad_wdr2
  la       x10, msg_s0
  addi     x10, x10, 192
  la       x11, msg_s1
  addi     x11, x11, 192
  jal      x1, mask_unmasked_wdr_512
  jal      x1, mask_unmasked_wdr_512

  jal      x1, sha512_init_state_masked
  la       x10, msg_s0
  la       x11, msg_s1
  li       x30, 2
  jal      x0, sha512_masked

/**
 * Converts 64-byte SHA-512 state shares in state_s0/state_s1 (efgh at 0, abcd at 32)
 * to big-endian stream byte order at 0(x12) and 0(x13) (abcd BE at 0, efgh BE at 32).
 */
state_to_be_masked_sha512:
  la       x2, bswap32_mask
  li       x3, 8
  bn.lid   x3, 0(x2)
  la       x2, swap32_in_64_mask
  li       x3, 9
  bn.lid   x3, 0(x2)

  /* WDR 0 of output (bytes 0..31): abcd from state + 32 */
  la       x2, state_s0
  addi     x2, x2, 32
  addi     x10, x12, 0
  jal      x1, reverse_and_bswap64_wdr

  la       x2, state_s1
  addi     x2, x2, 32
  addi     x10, x13, 0
  jal      x1, reverse_and_bswap64_wdr

  /* WDR 1 of output (bytes 32..63): efgh from state + 0 */
  la       x2, state_s0
  addi     x10, x12, 32
  jal      x1, reverse_and_bswap64_wdr

  la       x2, state_s1
  addi     x10, x13, 32
  jal      x0, reverse_and_bswap64_wdr

reverse_and_bswap64_wdr:
  li       x3, 0
  bn.lid   x3, 0(x2)
  bn.wsrr  w24, URND
  loopi    4, 2
    bn.rshi  w0,  w0,  w0 >> 192
    bn.rshi  w24, w0,  w24 >> 64
  bn.mov   w0, w24
  jal      x1, bswap64_w0
  bn.sid   x3, 0(x10)
  bn.wsrr  w0, URND
  bn.wsrr  w24, URND
  bn.xor   w31, w31, w31
  ret

/**
 * Initializes state_s0 and state_s1 with fresh boolean shares of SHA-512 IV.
 */
sha512_init_state_masked:
  la       x2,  sha512_iv
  la       x10, state_s0
  la       x11, state_s1
  jal      x1, mask_unmasked_wdr_512
  jal      x0, mask_unmasked_wdr_512

.data

.balign 32
sha512_iv:
  /* efgh: H[7], H[6], H[5], H[4] */
  .dword 0x5be0cd19137e2179, 0x1f83d9abfb41bd6b, 0x9b05688c2b3e6c1f, 0x510e527fade682d1
  /* abcd: H[3], H[2], H[1], H[0] */
  .dword 0xa54ff53a5f1d36f1, 0x3c6ef372fe94f82b, 0xbb67ae8584caa73b, 0x6a09e667f3bcc908

.balign 32
ipad_const:
  .word 0x36363636, 0x36363636, 0x36363636, 0x36363636
  .word 0x36363636, 0x36363636, 0x36363636, 0x36363636

.balign 32
opad_const:
  .word 0x5c5c5c5c, 0x5c5c5c5c, 0x5c5c5c5c, 0x5c5c5c5c
  .word 0x5c5c5c5c, 0x5c5c5c5c, 0x5c5c5c5c, 0x5c5c5c5c

/* WDR 2 & WDR 3 of outer HMAC-SHA512 block (bytes 192..255 of 256-byte outer message):
 * Byte 192 = 0x80, Bytes 193..251 = 0x00, Bytes 252..255 = 1536 bits (0x00000600 BE) */
.balign 32
hmac512_outer_pad_wdr2:
  .word 0x00000080, 0x00000000, 0x00000000, 0x00000000
  .word 0x00000000, 0x00000000, 0x00000000, 0x00000000
hmac512_outer_pad_wdr3:
  .word 0x00000000, 0x00000000, 0x00000000, 0x00000000
  .word 0x00000000, 0x00000000, 0x00000000, 0x00060000

.bss

/* Scratch buffers for masked HMAC message construction (160 bytes each) */
.balign 32
hmac_msg_s0:
  .zero 160

.balign 32
hmac_msg_s1:
  .zero 160
