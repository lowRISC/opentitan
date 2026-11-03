// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * @file
 * @brief Plain software implementation of Triple DES (TDES).
 *
 * WARNING: This implementation is a plain software implementation and is NOT
 * protected against fault injection (FI) or side-channel analysis (SCA)
 * attacks. Key shares are unmasked in software memory and DES rounds are
 * computed using standard table lookups without masking or FI redundancy.
 */

#include "sw/device/lib/crypto/include/tdes.h"

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/impl/cmvp.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/state.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/integrity.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('t', 'd', 's')

enum {
  /** Number of bytes in a TDES cipher block (64 bits). */
  kTdesBlockNumBytes = 8,
  /** Number of 32-bit words in a TDES cipher block. */
  kTdesBlockNumWords = kTdesBlockNumBytes / sizeof(uint32_t),
  /** Number of rounds in a single DES operation. */
  kDesNumRounds = 16,
  /** Key length in bytes for 2-key TDES without parity bits (112 bits). */
  kTdesKeyLen2KeyPackedBytes = 14,
  /** Key length in bytes for 2-key TDES with parity bits (128 bits). */
  kTdesKeyLen2KeyBytes = 16,
  /** Key length in bytes for 3-key TDES without parity bits (168 bits). */
  kTdesKeyLen3KeyPackedBytes = 21,
  /** Key length in bytes for 3-key TDES with parity bits (192 bits). */
  kTdesKeyLen3KeyBytes = 24,
  /** Maximum number of 32-bit words in a TDES key share. */
  kTdesKeyMaxWords = kTdesKeyLen3KeyBytes / sizeof(uint32_t),
};

/**
 * Type to represent a single 64-bit TDES block.
 */
typedef struct tdes_block {
  uint32_t data[kTdesBlockNumWords];
} tdes_block_t;

/**
 * Expanded TDES key schedule for EDE3 / EDE2 operations.
 */
typedef struct tdes_key_schedule {
  otcrypto_tdes_mode_t mode;
  uint64_t ks1[kDesNumRounds];
  uint64_t ks2[kDesNumRounds];
  uint64_t ks3[kDesNumRounds];
} tdes_key_schedule_t;

// DES Initial Permutation (IP) table (1-indexed, MSB = 1).
static const uint8_t kDesIp[64] = {
    58, 50, 42, 34, 26, 18, 10, 2, 60, 52, 44, 36, 28, 20, 12, 4,
    62, 54, 46, 38, 30, 22, 14, 6, 64, 56, 48, 40, 32, 24, 16, 8,
    57, 49, 41, 33, 25, 17, 9,  1, 59, 51, 43, 35, 27, 19, 11, 3,
    61, 53, 45, 37, 29, 21, 13, 5, 63, 55, 47, 39, 31, 23, 15, 7,
};

// DES Final Permutation (FP / IP^-1) table (1-indexed).
static const uint8_t kDesFp[64] = {
    40, 8, 48, 16, 56, 24, 64, 32, 39, 7, 47, 15, 55, 23, 63, 31,
    38, 6, 46, 14, 54, 22, 62, 30, 37, 5, 45, 13, 53, 21, 61, 29,
    36, 4, 44, 12, 52, 20, 60, 28, 35, 3, 43, 11, 51, 19, 59, 27,
    34, 2, 42, 10, 50, 18, 58, 26, 33, 1, 41, 9,  49, 17, 57, 25,
};

// DES Permuted Choice 1 (PC-1) table (64-bit key to 56-bit key).
static const uint8_t kDesPc1[56] = {
    57, 49, 41, 33, 25, 17, 9,  1,  58, 50, 42, 34, 26, 18, 10, 2,  59, 51, 43,
    35, 27, 19, 11, 3,  60, 52, 44, 36, 63, 55, 47, 39, 31, 23, 15, 7,  62, 54,
    46, 38, 30, 22, 14, 6,  61, 53, 45, 37, 29, 21, 13, 5,  28, 20, 12, 4,
};

// DES Permuted Choice 2 (PC-2) table (56-bit state to 48-bit round subkey).
static const uint8_t kDesPc2[48] = {
    14, 17, 11, 24, 1,  5,  3,  28, 15, 6,  21, 10, 23, 19, 12, 4,
    26, 8,  16, 7,  27, 20, 13, 2,  41, 52, 31, 37, 47, 55, 30, 40,
    51, 45, 33, 48, 44, 49, 39, 56, 34, 53, 46, 42, 50, 36, 29, 32,
};

// Left rotation schedule for 28-bit C and D halves per DES round.
static const uint8_t kDesRotations[kDesNumRounds] = {
    1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 1,
};

// DES Expansion (E) table (32-bit R to 48-bit expanded R).
static const uint8_t kDesE[48] = {
    32, 1,  2,  3,  4,  5,  4,  5,  6,  7,  8,  9,  8,  9,  10, 11,
    12, 13, 12, 13, 14, 15, 16, 17, 16, 17, 18, 19, 20, 21, 20, 21,
    22, 23, 24, 25, 24, 25, 26, 27, 28, 29, 28, 29, 30, 31, 32, 1,
};

// DES Permutation (P) table (32-bit S-box output to 32-bit Feistel output).
static const uint8_t kDesP[32] = {
    16, 7, 20, 21, 29, 12, 28, 17, 1,  15, 23, 26, 5,  18, 31, 10,
    2,  8, 24, 14, 32, 27, 3,  9,  19, 13, 30, 6,  22, 11, 4,  25,
};

// DES S-boxes S1..S8.
static const uint8_t kDesSbox[8][64] = {
    // S1
    {14, 4,  13, 1, 2,  15, 11, 8,  3,  10, 6,  12, 5,  9,  0, 7,
     0,  15, 7,  4, 14, 2,  13, 1,  10, 6,  12, 11, 9,  5,  3, 8,
     4,  1,  14, 8, 13, 6,  2,  11, 15, 12, 9,  7,  3,  10, 5, 0,
     15, 12, 8,  2, 4,  9,  1,  7,  5,  11, 3,  14, 10, 0,  6, 13},
    // S2
    {15, 1,  8,  14, 6,  11, 3,  4,  9,  7, 2,  13, 12, 0, 5,  10,
     3,  13, 4,  7,  15, 2,  8,  14, 12, 0, 1,  10, 6,  9, 11, 5,
     0,  14, 7,  11, 10, 4,  13, 1,  5,  8, 12, 6,  9,  3, 2,  15,
     13, 8,  10, 1,  3,  15, 4,  2,  11, 6, 7,  12, 0,  5, 14, 9},
    // S3
    {10, 0,  9,  14, 6, 3,  15, 5,  1,  13, 12, 7,  11, 4,  2,  8,
     13, 7,  0,  9,  3, 4,  6,  10, 2,  8,  5,  14, 12, 11, 15, 1,
     13, 6,  4,  9,  8, 15, 3,  0,  11, 1,  2,  12, 5,  10, 14, 7,
     1,  10, 13, 0,  6, 9,  8,  7,  4,  15, 14, 3,  11, 5,  2,  12},
    // S4
    {7,  13, 14, 3, 0,  6,  9,  10, 1,  2, 8, 5,  11, 12, 4,  15,
     13, 8,  11, 5, 6,  15, 0,  3,  4,  7, 2, 12, 1,  10, 14, 9,
     10, 6,  9,  0, 12, 11, 7,  13, 15, 1, 3, 14, 5,  2,  8,  4,
     3,  15, 0,  6, 10, 1,  13, 8,  9,  4, 5, 11, 12, 7,  2,  14},
    // S5
    {2,  12, 4,  1,  7,  10, 11, 6,  8,  5,  3,  15, 13, 0, 14, 9,
     14, 11, 2,  12, 4,  7,  13, 1,  5,  0,  15, 10, 3,  9, 8,  6,
     4,  2,  1,  11, 10, 13, 7,  8,  15, 9,  12, 5,  6,  3, 0,  14,
     11, 8,  12, 7,  1,  14, 2,  13, 6,  15, 0,  9,  10, 4, 5,  3},
    // S6
    {12, 1,  10, 15, 9, 2,  6,  8,  0,  13, 3,  4,  14, 7,  5,  11,
     10, 15, 4,  2,  7, 12, 9,  5,  6,  1,  13, 14, 0,  11, 3,  8,
     9,  14, 15, 5,  2, 8,  12, 3,  7,  0,  4,  10, 1,  13, 11, 6,
     4,  3,  2,  12, 9, 5,  15, 10, 11, 14, 1,  7,  6,  0,  8,  13},
    // S7
    {4,  11, 2,  14, 15, 0, 8,  13, 3,  12, 9, 7,  5,  10, 6, 1,
     13, 0,  11, 7,  4,  9, 1,  10, 14, 3,  5, 12, 2,  15, 8, 6,
     1,  4,  11, 13, 12, 3, 7,  14, 10, 15, 6, 8,  0,  5,  9, 2,
     6,  11, 13, 8,  1,  4, 10, 7,  9,  5,  0, 15, 14, 2,  3, 12},
    // S8
    {13, 2,  8,  4, 6,  15, 11, 1,  10, 9,  3,  14, 5,  0,  12, 7,
     1,  15, 13, 8, 10, 3,  7,  4,  12, 5,  6,  11, 0,  14, 9,  2,
     7,  11, 4,  1, 9,  12, 14, 2,  0,  6,  10, 13, 15, 3,  5,  8,
     2,  1,  14, 7, 4,  10, 8,  13, 15, 12, 9,  0,  3,  5,  6,  11},
};

/**
 * Permutes `in_bits` of `in` into `out_bits` according to 1-indexed `table`.
 */
static uint64_t tdes_permute(uint64_t in, size_t in_bits, const uint8_t *table,
                             size_t out_bits) {
  uint32_t in_hi = (uint32_t)(in >> 32);
  uint32_t in_lo = (uint32_t)in;
  uint64_t out = 0;
  for (size_t i = 0; i < out_bits; ++i) {
    uint32_t shift = (uint32_t)(in_bits - table[i]);
    uint32_t bit = (shift < 32U) ? ((in_lo >> shift) & 1U)
                                 : ((in_hi >> (shift - 32U)) & 1U);
    out = (out << 1) | (uint64_t)bit;
  }
  return out;
}

/**
 * Generates the 16 48-bit round subkeys for a single 64-bit DES key.
 */
static void tdes_subkey_schedule(uint64_t key64,
                                 uint64_t subkeys[kDesNumRounds]) {
  uint64_t cd = tdes_permute(key64, 64, kDesPc1, 56);
  uint32_t c = (uint32_t)((cd >> 28) & 0x0fffffffULL);
  uint32_t d = (uint32_t)(cd & 0x0fffffffULL);
  for (size_t r = 0; r < kDesNumRounds; ++r) {
    uint8_t sh = kDesRotations[r];
    c = ((c << sh) | (c >> (28U - sh))) & 0x0fffffffU;
    d = ((d << sh) | (d >> (28U - sh))) & 0x0fffffffU;
    uint64_t combined = (((uint64_t)c) << 28) | (uint64_t)d;
    subkeys[r] = tdes_permute(combined, 56, kDesPc2, 48);
  }
}

/**
 * Computes the DES Feistel function f(R, K).
 */
static uint32_t tdes_feistel(uint32_t r, uint64_t k48) {
  uint64_t er = tdes_permute((uint64_t)r, 32, kDesE, 48) ^ k48;
  uint32_t s_out = 0;
  for (size_t i = 0; i < 8; ++i) {
    uint8_t b6 = (uint8_t)((er >> 42) & 0x3fULL);
    er <<= 6;
    uint8_t row = (uint8_t)(((b6 & 0x20U) >> 4) | (b6 & 0x01U));
    uint8_t col = (uint8_t)((b6 >> 1) & 0x0fU);
    s_out = (s_out << 4) | (uint32_t)kDesSbox[i][row * 16U + col];
  }
  return (uint32_t)tdes_permute((uint64_t)s_out, 32, kDesP, 32);
}

/**
 * Encrypts or decrypts a single 64-bit block using DES.
 */
static uint64_t tdes_round_crypt_u64(uint64_t block,
                                     const uint64_t subkeys[kDesNumRounds],
                                     bool decrypt) {
  uint64_t ip = tdes_permute(block, 64, kDesIp, 64);
  uint32_t l = (uint32_t)(ip >> 32);
  uint32_t r = (uint32_t)(ip & 0xffffffffULL);
  for (size_t i = 0; i < kDesNumRounds; ++i) {
    size_t k_idx = decrypt ? (kDesNumRounds - 1 - i) : i;
    uint32_t next_l = r;
    uint32_t next_r = l ^ tdes_feistel(r, subkeys[k_idx]);
    l = next_l;
    r = next_r;
  }
  uint64_t pre_fp = (((uint64_t)r) << 32) | (uint64_t)l;
  return tdes_permute(pre_fp, 64, kDesFp, 64);
}

/**
 * Loads an 8-byte array as a big-endian 64-bit integer.
 */
static uint64_t bytes_to_u64_be(const uint8_t bytes[kTdesBlockNumBytes]) {
  return ((uint64_t)bytes[0] << 56) | ((uint64_t)bytes[1] << 48) |
         ((uint64_t)bytes[2] << 40) | ((uint64_t)bytes[3] << 32) |
         ((uint64_t)bytes[4] << 24) | ((uint64_t)bytes[5] << 16) |
         ((uint64_t)bytes[6] << 8) | (uint64_t)bytes[7];
}

/**
 * Stores a big-endian 64-bit integer into an 8-byte array.
 */
static void u64_be_to_bytes(uint64_t val, uint8_t bytes[kTdesBlockNumBytes]) {
  bytes[0] = (uint8_t)(val >> 56);
  bytes[1] = (uint8_t)(val >> 48);
  bytes[2] = (uint8_t)(val >> 40);
  bytes[3] = (uint8_t)(val >> 32);
  bytes[4] = (uint8_t)(val >> 24);
  bytes[5] = (uint8_t)(val >> 16);
  bytes[6] = (uint8_t)(val >> 8);
  bytes[7] = (uint8_t)val;
}

/**
 * Unpacks a 7-byte (56-bit) packed DES key into a 64-bit DES key with 7 key
 * bits in the upper 7 bits of each byte.
 */
static uint64_t unpack_tdes_56_to_64(const uint8_t k7[7]) {
  uint64_t k56 = ((uint64_t)k7[0] << 48) | ((uint64_t)k7[1] << 40) |
                 ((uint64_t)k7[2] << 32) | ((uint64_t)k7[3] << 24) |
                 ((uint64_t)k7[4] << 16) | ((uint64_t)k7[5] << 8) |
                 (uint64_t)k7[6];
  uint64_t k64 = 0;
  for (size_t i = 0; i < 8; ++i) {
    uint8_t seven_bits = (uint8_t)((k56 >> 49) & 0x7fULL);
    k56 <<= 7;
    k64 = (k64 << 8) | ((uint64_t)seven_bits << 1);
  }
  return k64;
}

/**
 * Encrypts a single 64-bit TDES block (EDE: E_K3(D_K2(E_K1(block)))).
 */
static void tdes_encrypt_block(const tdes_key_schedule_t *ks,
                               const tdes_block_t *in, tdes_block_t *out) {
  uint64_t b = bytes_to_u64_be((const uint8_t *)in->data);
  b = tdes_round_crypt_u64(b, ks->ks1, /*decrypt=*/false);
  b = tdes_round_crypt_u64(b, ks->ks2, /*decrypt=*/true);
  b = tdes_round_crypt_u64(b, ks->ks3, /*decrypt=*/false);
  u64_be_to_bytes(b, (uint8_t *)out->data);
}

/**
 * Decrypts a single 64-bit TDES block (DED: D_K1(E_K2(D_K3(block)))).
 */
static void tdes_decrypt_block(const tdes_key_schedule_t *ks,
                               const tdes_block_t *in, tdes_block_t *out) {
  uint64_t b = bytes_to_u64_be((const uint8_t *)in->data);
  b = tdes_round_crypt_u64(b, ks->ks3, /*decrypt=*/true);
  b = tdes_round_crypt_u64(b, ks->ks2, /*decrypt=*/false);
  b = tdes_round_crypt_u64(b, ks->ks1, /*decrypt=*/true);
  u64_be_to_bytes(b, (uint8_t *)out->data);
}

/**
 * Extracts and expands a TDES key from the blinded key struct.
 *
 * Note: This function unmasks the key shares into software memory to expand
 * the DES subkeys; it is NOT protected against side-channel analysis (SCA) or
 * fault injection (FI) attacks.
 *
 * @param blinded_key Blinded key struct.
 * @param tdes_mode Block cipher mode.
 * @param[out] ks Destination TDES key schedule.
 * @return Result of the operation.
 */
static status_t tdes_key_construct(otcrypto_blinded_key_t *blinded_key,
                                   const otcrypto_tdes_mode_t tdes_mode,
                                   tdes_key_schedule_t *ks) {
  // Key integrity check.
  if (otcrypto_integrity_blinded_key_check(blinded_key) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Hardware-backed sideload keys are not supported for software TDES.
  if (blinded_key->config.hw_backed != kHardenedBoolFalse) {
    return OTCRYPTO_BAD_ARGS;
  }

  switch (blinded_key->config.key_mode) {
    case kOtcryptoKeyModeTdesEcb:
      ks->mode = kOtcryptoTdesModeEcb;
      break;
    case kOtcryptoKeyModeTdesCbc:
      ks->mode = kOtcryptoTdesModeCbc;
      break;
    case kOtcryptoKeyModeTdesCfb:
      ks->mode = kOtcryptoTdesModeCfb;
      break;
    case kOtcryptoKeyModeTdesOfb:
      ks->mode = kOtcryptoTdesModeOfb;
      break;
    case kOtcryptoKeyModeTdesCtr:
      ks->mode = kOtcryptoTdesModeCtr;
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  if (ks->mode != tdes_mode) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Unmask the key words into a temporary buffer and expand the subkeys.
  size_t key_words = keyblob_share_num_words(blinded_key->config);
  if (key_words > kTdesKeyMaxWords) {
    return OTCRYPTO_BAD_ARGS;
  }
  uint32_t unmasked_key[kTdesKeyMaxWords] = {0};
  HARDENED_TRY(keyblob_key_unmask(blinded_key, key_words, unmasked_key));
  const uint8_t *key_bytes = (const uint8_t *)unmasked_key;

  uint64_t k1 = 0;
  uint64_t k2 = 0;
  uint64_t k3 = 0;
  switch (blinded_key->config.key_length) {
    case kTdesKeyLen2KeyBytes:
      k1 = bytes_to_u64_be(&key_bytes[0]);
      k2 = bytes_to_u64_be(&key_bytes[8]);
      k3 = k1;
      break;
    case kTdesKeyLen3KeyBytes:
      k1 = bytes_to_u64_be(&key_bytes[0]);
      k2 = bytes_to_u64_be(&key_bytes[8]);
      k3 = bytes_to_u64_be(&key_bytes[16]);
      break;
    case kTdesKeyLen2KeyPackedBytes:
      k1 = unpack_tdes_56_to_64(&key_bytes[0]);
      k2 = unpack_tdes_56_to_64(&key_bytes[7]);
      k3 = k1;
      break;
    case kTdesKeyLen3KeyPackedBytes:
      k1 = unpack_tdes_56_to_64(&key_bytes[0]);
      k2 = unpack_tdes_56_to_64(&key_bytes[7]);
      k3 = unpack_tdes_56_to_64(&key_bytes[14]);
      break;
    default:
      memset(unmasked_key, 0, sizeof(unmasked_key));
      return OTCRYPTO_BAD_ARGS;
  }

  tdes_subkey_schedule(k1, ks->ks1);
  tdes_subkey_schedule(k2, ks->ks2);
  tdes_subkey_schedule(k3, ks->ks3);

  memset(unmasked_key, 0, sizeof(unmasked_key));
  return OTCRYPTO_OK;
}

/**
 * Applies the specified mode of TDES padding to the block.
 *
 * @param padding_mode Padding mode.
 * @param partial_data_len Length of real input in this block (may be 0).
 * @param[out] block Destination padded block.
 * @return Result of the operation.
 */
static status_t tdes_padding_apply(otcrypto_tdes_padding_t padding_mode,
                                   const size_t partial_data_len,
                                   tdes_block_t *block) {
  char *padding = ((char *)block->data) + partial_data_len;
  size_t padding_len = kTdesBlockNumBytes - partial_data_len;
  switch (padding_mode) {
    case kOtcryptoTdesPaddingPkcs7:
      memset(padding, (uint8_t)padding_len, padding_len);
      break;
    case kOtcryptoTdesPaddingIso9797M2:
      memset(padding, 0x0, padding_len);
      padding[0] = (char)0x80;
      break;
    case kOtcryptoTdesPaddingNull:
      return OTCRYPTO_RECOV_ERR;
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  return OTCRYPTO_OK;
}

/**
 * Return the number of blocks for the input and padding mode.
 *
 * @param plaintext_len Length of plaintext in bytes.
 * @param padding Padding mode.
 * @param[out] num_blocks Number of TDES blocks required.
 * @return Result of the operation.
 */
static status_t num_padded_blocks_get(size_t plaintext_len,
                                      otcrypto_tdes_padding_t padding,
                                      size_t *num_blocks) {
  size_t num_full_blocks = plaintext_len / kTdesBlockNumBytes;

  switch (padding) {
    case kOtcryptoTdesPaddingPkcs7:
    case kOtcryptoTdesPaddingIso9797M2:
      if (plaintext_len > UINT32_MAX - kTdesBlockNumBytes) {
        return OTCRYPTO_BAD_ARGS;
      }
      *num_blocks = num_full_blocks + 1;
      break;
    case kOtcryptoTdesPaddingNull:
      if (num_full_blocks * kTdesBlockNumBytes != plaintext_len) {
        return OTCRYPTO_BAD_ARGS;
      }
      *num_blocks = num_full_blocks;
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  return OTCRYPTO_OK;
}

/**
 * Return the block at index `index` for the given input and padding mode.
 *
 * @param input Input data buffer.
 * @param padding Padding mode.
 * @param index Block index.
 * @param[out] block TDES block at `index`.
 * @return Result of the operation.
 */
static status_t get_block(const otcrypto_const_byte_buf_t *input,
                          otcrypto_tdes_padding_t padding, size_t index,
                          tdes_block_t *block) {
  size_t num_full_blocks = input->len / kTdesBlockNumBytes;

  if (index < num_full_blocks) {
    memcpy(block->data, &input->data[index * kTdesBlockNumBytes],
           kTdesBlockNumBytes);
    return OTCRYPTO_OK;
  }

  size_t partial_data_len = input->len % kTdesBlockNumBytes;
  memcpy(block->data, &input->data[index * kTdesBlockNumBytes],
         partial_data_len);
  return tdes_padding_apply(padding, partial_data_len, block);
}

otcrypto_status_t otcrypto_tdes_padded_plaintext_length(
    size_t plaintext_len, otcrypto_tdes_padding_t tdes_padding,
    size_t *padded_len) {
  OTCRYPTO_LOCKED_STATE_CHECK();
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (padded_len == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif
  size_t padded_nblocks;
  HARDENED_TRY(
      num_padded_blocks_get(plaintext_len, tdes_padding, &padded_nblocks));
  *padded_len = padded_nblocks * kTdesBlockNumBytes;
  return OTCRYPTO_OK;
}

/**
 * Processes one 64-bit TDES block according to mode and operation, updating
 * the running IV state in place.
 */
static status_t tdes_process_block(const tdes_key_schedule_t *ks,
                                   otcrypto_tdes_mode_t tdes_mode,
                                   otcrypto_tdes_operation_t tdes_operation,
                                   tdes_block_t *iv_state,
                                   const tdes_block_t *block_in,
                                   tdes_block_t *block_out) {
  switch (tdes_mode) {
    case kOtcryptoTdesModeEcb:
      if (tdes_operation == kOtcryptoTdesOperationEncrypt) {
        tdes_encrypt_block(ks, block_in, block_out);
      } else if (tdes_operation == kOtcryptoTdesOperationDecrypt) {
        tdes_decrypt_block(ks, block_in, block_out);
      } else {
        return OTCRYPTO_BAD_ARGS;
      }
      break;
    case kOtcryptoTdesModeCbc:
      if (tdes_operation == kOtcryptoTdesOperationEncrypt) {
        tdes_block_t xored;
        xored.data[0] = block_in->data[0] ^ iv_state->data[0];
        xored.data[1] = block_in->data[1] ^ iv_state->data[1];
        tdes_encrypt_block(ks, &xored, block_out);
        *iv_state = *block_out;
      } else if (tdes_operation == kOtcryptoTdesOperationDecrypt) {
        tdes_block_t dec;
        tdes_decrypt_block(ks, block_in, &dec);
        block_out->data[0] = dec.data[0] ^ iv_state->data[0];
        block_out->data[1] = dec.data[1] ^ iv_state->data[1];
        *iv_state = *block_in;
      } else {
        return OTCRYPTO_BAD_ARGS;
      }
      break;
    case kOtcryptoTdesModeCfb: {
      tdes_block_t enc_iv;
      tdes_encrypt_block(ks, iv_state, &enc_iv);
      block_out->data[0] = enc_iv.data[0] ^ block_in->data[0];
      block_out->data[1] = enc_iv.data[1] ^ block_in->data[1];
      if (tdes_operation == kOtcryptoTdesOperationEncrypt) {
        *iv_state = *block_out;
      } else if (tdes_operation == kOtcryptoTdesOperationDecrypt) {
        *iv_state = *block_in;
      } else {
        return OTCRYPTO_BAD_ARGS;
      }
      break;
    }
    case kOtcryptoTdesModeOfb:
      if (tdes_operation != kOtcryptoTdesOperationEncrypt &&
          tdes_operation != kOtcryptoTdesOperationDecrypt) {
        return OTCRYPTO_BAD_ARGS;
      }
      tdes_encrypt_block(ks, iv_state, iv_state);
      block_out->data[0] = iv_state->data[0] ^ block_in->data[0];
      block_out->data[1] = iv_state->data[1] ^ block_in->data[1];
      break;
    case kOtcryptoTdesModeCtr: {
      if (tdes_operation != kOtcryptoTdesOperationEncrypt &&
          tdes_operation != kOtcryptoTdesOperationDecrypt) {
        return OTCRYPTO_BAD_ARGS;
      }
      tdes_block_t keystream;
      tdes_encrypt_block(ks, iv_state, &keystream);
      block_out->data[0] = keystream.data[0] ^ block_in->data[0];
      block_out->data[1] = keystream.data[1] ^ block_in->data[1];
      uint64_t ctr = bytes_to_u64_be((const uint8_t *)iv_state->data);
      ctr += 1ULL;
      u64_be_to_bytes(ctr, (uint8_t *)iv_state->data);
      break;
    }
    default:
      return OTCRYPTO_BAD_ARGS;
  }
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_tdes_padding_strip(
    otcrypto_byte_buf_t *padded_plaintext, otcrypto_tdes_padding_t tdes_padding,
    size_t *plaintext_len) {
  OTCRYPTO_LOCKED_STATE_CHECK();
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (padded_plaintext == NULL || padded_plaintext->data == NULL ||
      plaintext_len == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  // Input must be a non-zero multiple of the TDES block size.
  if (padded_plaintext->len == 0 ||
      padded_plaintext->len % kTdesBlockNumBytes != 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  const uint8_t *data = (const uint8_t *)padded_plaintext->data;
  size_t len = padded_plaintext->len;
  const uint8_t *last_block = data + len - kTdesBlockNumBytes;

  switch (tdes_padding) {
    case kOtcryptoTdesPaddingPkcs7: {
      uint8_t pad_byte = last_block[kTdesBlockNumBytes - 1];
      uint32_t valid = (uint32_t)((uint8_t)(pad_byte - 1) < kTdesBlockNumBytes);

      for (size_t i = 0; i < kTdesBlockNumBytes; i++) {
        uint32_t is_pad = (uint32_t)(i + pad_byte >= kTdesBlockNumBytes);
        uint32_t matches = (uint32_t)(last_block[i] == pad_byte);
        valid &= (1u - is_pad) | matches;
      }

      *plaintext_len = len - pad_byte;
      otcrypto_status_t status = OTCRYPTO_OK;
      status.value ^= (int32_t)(((uint32_t)OTCRYPTO_OK.value ^
                                 (uint32_t)OTCRYPTO_BAD_ARGS.value) &
                                (valid - 1));
      return status;
    }
    case kOtcryptoTdesPaddingIso9797M2: {
      uint32_t valid = 1;
      uint32_t found_marker = 0;
      uint32_t marker_idx = 0;
      for (size_t i = kTdesBlockNumBytes - 1; i < kTdesBlockNumBytes; i--) {
        uint8_t byte = last_block[i];
        uint32_t is_zero = (uint32_t)(byte == 0x00);
        uint32_t is_marker = (uint32_t)(byte == 0x80);
        uint32_t searching = (uint32_t)(found_marker == 0);
        valid &= 1u - (searching & (1u - (is_zero | is_marker)));
        uint32_t record = searching & is_marker;
        uint32_t rec_mask = (uint32_t)(-(int32_t)record);
        marker_idx = (marker_idx & ~rec_mask) | ((uint32_t)i & rec_mask);
        found_marker |= record;
      }
      valid &= found_marker;
      *plaintext_len = len - kTdesBlockNumBytes + marker_idx;
      otcrypto_status_t status = {.value = OTCRYPTO_OK.value};
      status.value ^= (int32_t)(((uint32_t)OTCRYPTO_OK.value ^
                                 (uint32_t)OTCRYPTO_BAD_ARGS.value) &
                                (valid - 1));
      return status;
    }
    case kOtcryptoTdesPaddingNull:
      return OTCRYPTO_BAD_ARGS;
    default:
      return OTCRYPTO_BAD_ARGS;
  }
}

otcrypto_status_t otcrypto_tdes(otcrypto_blinded_key_t *key,
                                otcrypto_word32_buf_t *iv,
                                otcrypto_tdes_mode_t tdes_mode,
                                otcrypto_tdes_operation_t tdes_operation,
                                const otcrypto_const_byte_buf_t *cipher_input,
                                otcrypto_tdes_padding_t tdes_padding,
                                otcrypto_byte_buf_t *cipher_output) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_TDES);
  OTCRYPTO_LOCKED_STATE_CHECK();
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (key == NULL || key->keyblob == NULL ||
      (tdes_mode != kOtcryptoTdesModeEcb && (iv == NULL || iv->data == NULL)) ||
      (cipher_input == NULL ||
       (cipher_input->data == NULL && cipher_input->len != 0)) ||
      (cipher_output == NULL || cipher_output->data == NULL)) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  // Calculate the number of blocks for the input, including padding for
  // encryption.
  size_t input_nblocks = 0;
  if (tdes_operation == kOtcryptoTdesOperationEncrypt) {
    HARDENED_TRY(
        num_padded_blocks_get(cipher_input->len, tdes_padding, &input_nblocks));
  } else if (tdes_operation == kOtcryptoTdesOperationDecrypt) {
    if (cipher_input->len % kTdesBlockNumBytes != 0) {
      return OTCRYPTO_BAD_ARGS;
    }
    input_nblocks = cipher_input->len / kTdesBlockNumBytes;
  } else {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check input/output lengths.
  if (input_nblocks == 0 ||
      cipher_output->len != input_nblocks * kTdesBlockNumBytes) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Construct the IV and check its length. ECB mode ignores the IV.
  tdes_block_t tdes_iv = {{0}};
  if (tdes_mode != kOtcryptoTdesModeEcb) {
    if (iv->len != kTdesBlockNumWords) {
      return OTCRYPTO_BAD_ARGS;
    }
    memcpy(tdes_iv.data, iv->data, kTdesBlockNumBytes);
  }

  // Parse and expand the TDES key (plain software, not FI/SCA protected).
  tdes_key_schedule_t ks;
  HARDENED_TRY(tdes_key_construct(key, tdes_mode, &ks));

  tdes_block_t block_in;
  tdes_block_t block_out;
  for (size_t i = 0; i < input_nblocks; ++i) {
    HARDENED_TRY(get_block(cipher_input, tdes_padding, i, &block_in));
    HARDENED_TRY(tdes_process_block(&ks, tdes_mode, tdes_operation, &tdes_iv,
                                    &block_in, &block_out));
    memcpy(&cipher_output->data[i * kTdesBlockNumBytes], block_out.data,
           kTdesBlockNumBytes);
  }

  memset(&ks, 0, sizeof(ks));

  if (tdes_mode != kOtcryptoTdesModeEcb) {
    memcpy(iv->data, tdes_iv.data, kTdesBlockNumBytes);
  }

  return otcrypto_eval_exit(OTCRYPTO_OK);
}
