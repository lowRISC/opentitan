/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.globl hkdf_sha384_masked
.globl hkdf_extract_sha384_masked
.globl hkdf_expand_sha384_masked

.text

/**
 * Masked HKDF-SHA384 (RFC 5869) for OTBN.
 *
 * Computes:
 *   1. HKDF-Extract(salt, IKM) -> (prk_s0, prk_s1)   [48 bytes, zero-padded to 64B]
 *   2. HKDF-Expand(PRK, info, L) -> (okm_s0, okm_s1) [48*N bytes contiguous]
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
 *   - num_okm_blocks (4B,   aligned 4) : Number of 48-byte OKM blocks N (1 <= N <= 6)
 *   - prk_s0         (64B,  aligned 32): Output Share 0 of extracted PRK (48B + 16B zero)
 *   - prk_s1         (64B,  aligned 32): Output Share 1 of extracted PRK (48B + 16B zero)
 *   - okm_s0         (288B, aligned 32): Output Share 0 of expanded OKM (48*N bytes)
 *   - okm_s1         (288B, aligned 32): Output Share 1 of expanded OKM (48*N bytes)
 *   - msg_s0         (>=384B, aligned 32): Scratch message Share 0 buffer for SHA-384
 *   - msg_s1         (>=384B, aligned 32): Scratch message Share 1 buffer for SHA-384
 *   - state_s0       (64B,  aligned 32): Hash state Share 0 buffer for SHA-384
 *   - state_s1       (64B,  aligned 32): Hash state Share 1 buffer for SHA-384
 */
hkdf_sha384_masked:
  jal      x1, hkdf_extract_sha384_masked
  jal      x0, hkdf_expand_sha384_masked

/**
 * Masked HKDF-Extract: PRK = HMAC-SHA384(salt, IKM).
 */
hkdf_extract_sha384_masked:
  /* Copy ikm_s0/ikm_s1 (128B = 4 WDRs) to hmac_msg_s0/hmac_msg_s1 with fresh URND re-masking */
  la       x8,  ikm_s0
  la       x9,  ikm_s1
  la       x10, hmac_msg_s0
  la       x11, hmac_msg_s1
  bn.xor   w22, w22, w22
  loopi    4, 2
    jal      x1, remask_shared_wdr_384
    nop

  /* Inner HMAC key block: msg[0..127] = (salt ^ ipad) shared with URND */
  la       x12, ipad_const
  jal      x1, prepare_salt_key_block_384

  /* Run inner HMAC hash on IKM */
  la       x2, ikm_len
  lw       x14, 0(x2)
  jal      x1, hmac_sha384_inner

  /* Outer HMAC key block: msg[0..127] = (salt ^ opad) shared with URND */
  la       x12, opad_const
  jal      x1, prepare_salt_key_block_384

  /* Run outer HMAC hash on inner digest */
  jal      x1, hmac_sha384_outer

  /* Convert final state shares to big-endian stream bytes in prk_s0 / prk_s1 (48B + 16B zero share) */
  la       x12, prk_s0
  la       x13, prk_s1
  jal      x0, state_to_be_masked_sha384

/**
 * Masked HKDF-Expand: OKM = T(1) || T(2) || ... || T(N)
 * where T(i) = HMAC-SHA384(PRK, T(i-1) || info || byte(i)).
 */
hkdf_expand_sha384_masked:
  li       x24, 1               /* x24 <= block counter i = 1 */
  la       x2, num_okm_blocks
  lw       x25, 0(x2)           /* x25 <= remaining blocks count */
  la       x26, okm_s0          /* x26 <= pointer to okm_s0 block i */
  la       x27, okm_s1          /* x27 <= pointer to okm_s1 block i */

.L_expand384_loop:
  /* Zero out hmac_msg_s0 (5 WDRs = 160 bytes) */
  la       x12, hmac_msg_s0
  bn.xor   w31, w31, w31
  li       x3, 31
  loopi    5, 2
    bn.sid   x3, 0(x12++)
    nop

  la       x2, info_len
  lw       x14, 0(x2)

  li       x2, 1
  bne      x24, x2, .L_expand384_i_gt_1

  /* For iteration i == 1, write info || 0x01 at the start of hmac_msg_s0 */
  addi     x14, x14, 1
  la       x12, hmac_msg_s0
  jal      x1, write_info_and_counter_384
  jal      x0, .L_expand384_mask_msg

.L_expand384_i_gt_1:
  /* For iterations i > 1, reserve 48B for T(i-1) and write info || byte(i) at offset 48 */
  addi     x14, x14, 49
  la       x12, hmac_msg_s0
  addi     x12, x12, 48
  jal      x1, write_info_and_counter_384

.L_expand384_mask_msg:
  /* Mask all 5 WDRs (160B) of hmac_msg_s0 with fresh URND into Share 0 and Share 1 */
  la       x2,  hmac_msg_s0
  la       x10, hmac_msg_s0
  la       x11, hmac_msg_s1
  loopi    5, 2
    jal      x1, mask_unmasked_wdr_384
    nop

  /* If i > 1, XOR T(i-1) (12 words = 48B) from okm_s0/s1[i-1] into hmac_msg_s0/s1[0..47] */
  li       x2, 1
  beq      x24, x2, .L_expand384_run_hmac

  addi     x2,  x26, -48
  addi     x7,  x27, -48
  la       x12, hmac_msg_s0
  la       x16, hmac_msg_s1
  li       x21, 12
.L_expand384_xor_t_prev:
  lw       x5,  0(x2)
  lw       x18, 0(x12)
  xor      x5,  x5, x18
  sw       x5,  0(x12)
  li       x5,  0
  li       x18, 0
  lw       x6,  0(x7)
  lw       x19, 0(x16)
  xor      x6,  x6, x19
  sw       x6,  0(x16)
  li       x6,  0
  li       x19, 0
  addi     x2,  x2,  4
  addi     x7,  x7,  4
  addi     x12, x12, 4
  addi     x16, x16, 4
  addi     x21, x21, -1
  bne      x21, x0, .L_expand384_xor_t_prev

.L_expand384_run_hmac:
  /* Inner HMAC key block: msg[0..127] = (PRK_padded ^ ipad) */
  la       x12, ipad_const
  jal      x1, prepare_prk_key_block_384

  /* Run inner HMAC hash on M_i (length in x14) */
  jal      x1, hmac_sha384_inner

  /* Outer HMAC key block: msg[0..127] = (PRK_padded ^ opad) */
  la       x12, opad_const
  jal      x1, prepare_prk_key_block_384

  /* Run outer HMAC hash */
  jal      x1, hmac_sha384_outer

  /* Store T(i) in big-endian byte stream order to scratch msg_s0 / msg_s1 */
  la       x12, msg_s0
  la       x13, msg_s1
  jal      x1, state_to_be_masked_sha384

  /* Copy 48B (12 words) from msg_s0/s1 to contiguous okm_s0/s1 at x26/x27 */
  la       x2, msg_s0
  la       x7, msg_s1
  li       x21, 12
.L_expand384_copy_okm:
  lw       x5, 0(x2)
  sw       x5, 0(x26)
  li       x5, 0
  lw       x6, 0(x7)
  sw       x6, 0(x27)
  li       x6, 0
  addi     x2,  x2,  4
  addi     x7,  x7,  4
  addi     x26, x26, 4
  addi     x27, x27, 4
  addi     x21, x21, -1
  bne      x21, x0, .L_expand384_copy_okm

  /* Loop for next block */
  addi     x24, x24, 1
  addi     x25, x25, -1
  bne      x25, x0, .L_expand384_loop

  ret

/**
 * Prepares 128-byte masked key block from unmasked `salt` (4 WDRs) and pad at 0(x12).
 */
prepare_salt_key_block_384:
  la       x2, salt
  la       x10, msg_s0
  la       x11, msg_s1
  li       x5, 22
  bn.lid   x5, 0(x12)
  loopi    4, 2
    jal      x1, mask_unmasked_wdr_xor_w22_384
    nop
  bn.wsrr  w22, URND
  bn.xor   w31, w31, w31
  ret

/**
 * Prepares 128-byte masked key block from masked 64-byte `(prk_s0, prk_s1)`
 * (where bytes 48..63 are already boolean-shared zero) and pad constant at 0(x12).
 */
prepare_prk_key_block_384:
  la       x8,  prk_s0
  la       x9,  prk_s1
  la       x10, msg_s0
  la       x11, msg_s1
  li       x5, 22
  bn.lid   x5, 0(x12)
  /* WDR 0 & WDR 1 (bytes 0..63): PRK_padded ^ pad */
  jal      x1, remask_shared_wdr_384
  jal      x1, remask_shared_wdr_384
  /* WDR 2 & WDR 3 (bytes 64..127): 0 ^ pad = pad */
  addi     x2, x12, 0
  jal      x1, mask_unmasked_wdr_384
  addi     x2, x12, 0
  jal      x0, mask_unmasked_wdr_384

/**
 * Writes unmasked `info` (length dmem[info_len]) followed by counter byte `x24`
 * into zero-initialized buffer starting at 0(x12).
 *
 * Preserves: x12, x14, x16, x24, x25, x26, x27
 */
write_info_and_counter_384:
  la       x2, info_len
  lw       x15, 0(x2)
  la       x18, info
  addi     x2, x12, 0
  li       x21, 22

.L_info384_word_loop:
  addi     x17, x15, -4
  srli     x17, x17, 31
  bne      x17, x0, .L_info384_partial
  lw       x5, 0(x18)
  sw       x5, 0(x2)
  jal      x0, .L_info384_word_next

.L_info384_partial:
  srli     x17, x15, 31
  bne      x17, x0, .L_info384_word_next

  bne      x15, x0, .L_info384_partial_nonzero
  sw       x24, 0(x2)
  jal      x0, .L_info384_word_next

.L_info384_partial_nonzero:
  lw       x5, 0(x18)

  addi     x17, x15, -1
  addi     x7, x0, 0xff
  slli     x8, x24, 8
  beq      x17, x0, .L_info384_store_partial

  addi     x17, x15, -2
  lui      x7, 0x10
  addi     x7, x7, -1
  slli     x8, x24, 16
  beq      x17, x0, .L_info384_store_partial

  lui      x7, 0x1000
  addi     x7, x7, -1
  slli     x8, x24, 24

.L_info384_store_partial:
  and      x5, x5, x7
  or       x5, x5, x8
  sw       x5, 0(x2)

.L_info384_word_next:
  addi     x2,  x2,  4
  addi     x18, x18, 4
  addi     x15, x15, -4
  addi     x21, x21, -1
  bne      x21, x0, .L_info384_word_loop
  ret

/**
 * Pads boolean-masked message in hmac_msg_s0/hmac_msg_s1 (length x14 bytes)
 * into msg_s0[128..383] / msg_s1[128..383], initializes SHA-384 state shares,
 * and tail-calls sha384_masked for 2 or 3 blocks.
 */
hmac_sha384_inner:
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

.L_hmac384_inner_word_loop:
  addi     x17, x15, -4
  srli     x17, x17, 31
  bne      x17, x0, .L_hmac384_inner_partial
  lw       x5, 0(x12)
  sw       x5, 0(x10)
  li       x5, 0
  lw       x6, 0(x13)
  sw       x6, 0(x11)
  li       x6, 0
  jal      x0, .L_hmac384_inner_word_next

.L_hmac384_inner_partial:
  srli     x17, x15, 31
  bne      x17, x0, .L_hmac384_inner_word_next

  bne      x15, x0, .L_hmac384_inner_partial_nonzero
  lw       x18, 0(x10)
  xori     x18, x18, 0x80
  sw       x18, 0(x10)
  li       x18, 0
  jal      x0, .L_hmac384_inner_word_next

.L_hmac384_inner_partial_nonzero:
  addi     x17, x15, -1
  addi     x7, x0, 0xff
  lui      x8, 0x8
  beq      x17, x0, .L_hmac384_inner_apply_pad

  addi     x17, x15, -2
  lui      x7, 0x10
  addi     x7, x7, -1
  lui      x8, 0x800
  beq      x17, x0, .L_hmac384_inner_apply_pad

  lui      x7, 0x1000
  addi     x7, x7, -1
  lui      x8, 0x80000

.L_hmac384_inner_apply_pad:
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

.L_hmac384_inner_word_next:
  addi     x10, x10, 4
  addi     x11, x11, 4
  addi     x12, x12, 4
  addi     x13, x13, 4
  addi     x15, x15, -4
  addi     x21, x21, -1
  bne      x21, x0, .L_hmac384_inner_word_loop

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
  bne      x17, x0, .L_hmac384_inner_2blocks
  li       x30, 3
  la       x10, msg_s0
  addi     x10, x10, 380
  jal      x0, .L_hmac384_inner_store_len

.L_hmac384_inner_2blocks:
  li       x30, 2
  la       x10, msg_s0
  addi     x10, x10, 252

.L_hmac384_inner_store_len:
  lw       x5, 0(x10)
  xor      x5, x5, x8
  sw       x5, 0(x10)
  li       x5, 0

  jal      x1, sha384_init_state_masked
  la       x10, msg_s0
  la       x11, msg_s1
  jal      x0, sha384_masked

/**
 * Runs outer HMAC-SHA384 hash on 48-byte inner digest in state_s0/state_s1.
 */
hmac_sha384_outer:
  /* Convert 48B inner digest (+ 16B masked zero) to msg_s0+128 / msg_s1+128 */
  la       x12, msg_s0
  addi     x12, x12, 128
  la       x13, msg_s1
  addi     x13, x13, 128
  jal      x1, state_to_be_masked_sha384

  /* XOR 0x80 padding byte into Share 0 at offset 128 + 48 = 176 */
  la       x10, msg_s0
  lw       x5, 176(x10)
  xori     x5, x5, 0x80
  sw       x5, 176(x10)
  li       x5, 0

  /* Write WDR 2 (offset 192: zeros) and WDR 3 (offset 224: length = 1408 bits = 0x0580) */
  la       x2,  hmac384_outer_pad_wdr2
  la       x10, msg_s0
  addi     x10, x10, 192
  la       x11, msg_s1
  addi     x11, x11, 192
  jal      x1, mask_unmasked_wdr_384
  jal      x1, mask_unmasked_wdr_384

  jal      x1, sha384_init_state_masked
  la       x10, msg_s0
  la       x11, msg_s1
  li       x30, 2
  jal      x0, sha384_masked

/**
 * Re-masks 32B shares from 0(x8++) / 0(x9++) with fresh URND and XORs w22 into Share 0,
 * storing Share 0 to 0(x10++) and Share 1 to 0(x11++).
 */
remask_shared_wdr_384:
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
mask_unmasked_wdr_384:
  bn.xor   w22, w22, w22
mask_unmasked_wdr_xor_w22_384:
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
 * Converts SHA-384 state shares in state_s0/state_s1 to 48-byte big-endian
 * stream byte order at 0(x12) and 0(x13), with bytes 48..63 masked as zero.
 */
state_to_be_masked_sha384:
  la       x2, bswap32_mask
  li       x3, 8
  bn.lid   x3, 0(x2)
  la       x2, swap32_in_64_mask
  li       x3, 9
  bn.lid   x3, 0(x2)

  /* WDR 0 of output (bytes 0..31): abcd from state + 32 */
  la       x2, state_s0
  addi     x2, x2, 32
  jal      x1, reverse_and_bswap64_to_w0
  bn.sid   x3, 0(x12)
  bn.wsrr  w0, URND

  la       x2, state_s1
  addi     x2, x2, 32
  jal      x1, reverse_and_bswap64_to_w0
  bn.sid   x3, 0(x13)
  bn.wsrr  w0, URND

  /* WDR 1 of output (bytes 32..47: ef from state + 0; bytes 48..63: masked zero) */
  bn.wsrr  w25, URND            /* fresh mask R_hi for upper 128 bits */

  la       x2, state_s0
  jal      x1, reverse_and_bswap64_to_w0
  bn.rshi  w0,  w0,  w31 >> 128
  bn.rshi  w0,  w25, w0 >> 128
  bn.sid   x3, 32(x12)
  bn.wsrr  w0, URND

  la       x2, state_s1
  jal      x1, reverse_and_bswap64_to_w0
  bn.rshi  w0,  w0,  w31 >> 128
  bn.rshi  w0,  w25, w0 >> 128
  bn.sid   x3, 32(x13)
  bn.wsrr  w0, URND
  bn.wsrr  w25, URND
  bn.xor   w31, w31, w31
  ret

reverse_and_bswap64_to_w0:
  li       x3, 0
  bn.lid   x3, 0(x2)
  bn.wsrr  w24, URND
  loopi    4, 2
    bn.rshi  w0,  w0,  w0 >> 192
    bn.rshi  w24, w0,  w24 >> 64
  bn.mov   w0, w24
  jal      x1, bswap64_w0
  bn.wsrr  w24, URND
  bn.xor   w31, w31, w31
  ret

/**
 * Initializes state_s0 and state_s1 with fresh boolean shares of SHA-384 IV.
 */
sha384_init_state_masked:
  la       x2,  sha384_iv
  la       x10, state_s0
  la       x11, state_s1
  jal      x1, mask_unmasked_wdr_384
  jal      x0, mask_unmasked_wdr_384

.data

.balign 32
sha384_iv:
  /* efgh: H[7], H[6], H[5], H[4] */
  .dword 0x47b5481dbefa4fa4, 0xdb0c2e0d64f98fa7, 0x8eb44a8768581511, 0x67332667ffc00b31
  /* abcd: H[3], H[2], H[1], H[0] */
  .dword 0x152fecd8f70e5939, 0x9159015a3070dd17, 0x629a292a367cd507, 0xcbbb9d5dc1059ed8

.balign 32
ipad_const:
  .word 0x36363636, 0x36363636, 0x36363636, 0x36363636
  .word 0x36363636, 0x36363636, 0x36363636, 0x36363636

.balign 32
opad_const:
  .word 0x5c5c5c5c, 0x5c5c5c5c, 0x5c5c5c5c, 0x5c5c5c5c
  .word 0x5c5c5c5c, 0x5c5c5c5c, 0x5c5c5c5c, 0x5c5c5c5c

/* WDR 2 & WDR 3 of outer HMAC-SHA384 block (bytes 192..255 of 256-byte outer message):
 * Bytes 192..251 = 0x00, Bytes 252..255 = 1408 bits (0x00000580 BE -> 0x80050000 LE) */
.balign 32
hmac384_outer_pad_wdr2:
  .word 0x00000000, 0x00000000, 0x00000000, 0x00000000
  .word 0x00000000, 0x00000000, 0x00000000, 0x00000000
hmac384_outer_pad_wdr3:
  .word 0x00000000, 0x00000000, 0x00000000, 0x00000000
  .word 0x00000000, 0x00000000, 0x00000000, 0x80050000

.bss

/* Scratch buffers for masked HMAC message construction (160 bytes each) */
.balign 32
hmac_msg_s0:
  .zero 160

.balign 32
hmac_msg_s1:
  .zero 160
