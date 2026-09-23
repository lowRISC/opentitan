// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/sha2/hkdf.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/drivers/rv_core_ibex.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/sha2/sha256.h"
#include "sw/device/lib/crypto/impl/sha2/sha384.h"
#include "sw/device/lib/crypto/impl/sha2/sha512.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/cryptolib_build_info.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/integrity.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('s', '2', 'k')

enum {
  kHkdfMaxDigestWords = 16,
  kHkdfMaxBlockBytes = 128,
  kHkdfMaxIkmWords = 128,
};

OTBN_DECLARE_APP_SYMBOLS(run_hkdf_sha256);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha256, salt);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha256, ikm_s0);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha256, ikm_s1);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha256, ikm_len);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha256, info);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha256, info_len);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha256, num_okm_blocks);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha256, prk_s0);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha256, prk_s1);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha256, okm_s0);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha256, okm_s1);

OTBN_DECLARE_APP_SYMBOLS(run_hkdf_sha384);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha384, salt);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha384, ikm_s0);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha384, ikm_s1);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha384, ikm_len);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha384, info);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha384, info_len);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha384, num_okm_blocks);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha384, prk_s0);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha384, prk_s1);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha384, okm_s0);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha384, okm_s1);

OTBN_DECLARE_APP_SYMBOLS(run_hkdf_sha512);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha512, salt);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha512, ikm_s0);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha512, ikm_s1);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha512, ikm_len);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha512, info);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha512, info_len);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha512, num_okm_blocks);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha512, prk_s0);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha512, prk_s1);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha512, okm_s0);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha512, okm_s1);

typedef struct hkdf_otbn_app_cfg {
  otbn_addr_t addr_salt;
  otbn_addr_t addr_ikm_s0;
  otbn_addr_t addr_ikm_s1;
  otbn_addr_t addr_ikm_len;
  otbn_addr_t addr_info;
  otbn_addr_t addr_info_len;
  otbn_addr_t addr_num_okm_blocks;
  otbn_addr_t addr_prk_s0;
  otbn_addr_t addr_prk_s1;
  otbn_addr_t addr_okm_s0;
  otbn_addr_t addr_okm_s1;
  size_t digest_words;
  size_t block_words;
  size_t ikm_words;
  size_t max_ikm_bytes;
  size_t max_info_bytes;
  size_t max_okm_blocks;
} hkdf_otbn_app_cfg_t;

static status_t get_otbn_app_cfg(otcrypto_key_mode_t key_mode,
                                 hkdf_otbn_app_cfg_t *cfg) {
  switch (launder32(key_mode)) {
    case kOtcryptoKeyModeHmacSha256:
      *cfg = (hkdf_otbn_app_cfg_t){
          .addr_salt = OTBN_ADDR_T_INIT(run_hkdf_sha256, salt),
          .addr_ikm_s0 = OTBN_ADDR_T_INIT(run_hkdf_sha256, ikm_s0),
          .addr_ikm_s1 = OTBN_ADDR_T_INIT(run_hkdf_sha256, ikm_s1),
          .addr_ikm_len = OTBN_ADDR_T_INIT(run_hkdf_sha256, ikm_len),
          .addr_info = OTBN_ADDR_T_INIT(run_hkdf_sha256, info),
          .addr_info_len = OTBN_ADDR_T_INIT(run_hkdf_sha256, info_len),
          .addr_num_okm_blocks =
              OTBN_ADDR_T_INIT(run_hkdf_sha256, num_okm_blocks),
          .addr_prk_s0 = OTBN_ADDR_T_INIT(run_hkdf_sha256, prk_s0),
          .addr_prk_s1 = OTBN_ADDR_T_INIT(run_hkdf_sha256, prk_s1),
          .addr_okm_s0 = OTBN_ADDR_T_INIT(run_hkdf_sha256, okm_s0),
          .addr_okm_s1 = OTBN_ADDR_T_INIT(run_hkdf_sha256, okm_s1),
          .digest_words = 8,
          .block_words = 16,
          .ikm_words = 24,
          .max_ikm_bytes = 96,
          .max_info_bytes = 86,
          .max_okm_blocks = 8,
      };
      return OTCRYPTO_OK;
    case kOtcryptoKeyModeHmacSha384:
      *cfg = (hkdf_otbn_app_cfg_t){
          .addr_salt = OTBN_ADDR_T_INIT(run_hkdf_sha384, salt),
          .addr_ikm_s0 = OTBN_ADDR_T_INIT(run_hkdf_sha384, ikm_s0),
          .addr_ikm_s1 = OTBN_ADDR_T_INIT(run_hkdf_sha384, ikm_s1),
          .addr_ikm_len = OTBN_ADDR_T_INIT(run_hkdf_sha384, ikm_len),
          .addr_info = OTBN_ADDR_T_INIT(run_hkdf_sha384, info),
          .addr_info_len = OTBN_ADDR_T_INIT(run_hkdf_sha384, info_len),
          .addr_num_okm_blocks =
              OTBN_ADDR_T_INIT(run_hkdf_sha384, num_okm_blocks),
          .addr_prk_s0 = OTBN_ADDR_T_INIT(run_hkdf_sha384, prk_s0),
          .addr_prk_s1 = OTBN_ADDR_T_INIT(run_hkdf_sha384, prk_s1),
          .addr_okm_s0 = OTBN_ADDR_T_INIT(run_hkdf_sha384, okm_s0),
          .addr_okm_s1 = OTBN_ADDR_T_INIT(run_hkdf_sha384, okm_s1),
          .digest_words = 12,
          .block_words = 32,
          .ikm_words = 32,
          .max_ikm_bytes = 111,
          .max_info_bytes = 86,
          .max_okm_blocks = 6,
      };
      return OTCRYPTO_OK;
    case kOtcryptoKeyModeHmacSha512:
      *cfg = (hkdf_otbn_app_cfg_t){
          .addr_salt = OTBN_ADDR_T_INIT(run_hkdf_sha512, salt),
          .addr_ikm_s0 = OTBN_ADDR_T_INIT(run_hkdf_sha512, ikm_s0),
          .addr_ikm_s1 = OTBN_ADDR_T_INIT(run_hkdf_sha512, ikm_s1),
          .addr_ikm_len = OTBN_ADDR_T_INIT(run_hkdf_sha512, ikm_len),
          .addr_info = OTBN_ADDR_T_INIT(run_hkdf_sha512, info),
          .addr_info_len = OTBN_ADDR_T_INIT(run_hkdf_sha512, info_len),
          .addr_num_okm_blocks =
              OTBN_ADDR_T_INIT(run_hkdf_sha512, num_okm_blocks),
          .addr_prk_s0 = OTBN_ADDR_T_INIT(run_hkdf_sha512, prk_s0),
          .addr_prk_s1 = OTBN_ADDR_T_INIT(run_hkdf_sha512, prk_s1),
          .addr_okm_s0 = OTBN_ADDR_T_INIT(run_hkdf_sha512, okm_s0),
          .addr_okm_s1 = OTBN_ADDR_T_INIT(run_hkdf_sha512, okm_s1),
          .digest_words = 16,
          .block_words = 32,
          .ikm_words = 32,
          .max_ikm_bytes = 111,
          .max_info_bytes = 86,
          .max_okm_blocks = 4,
      };
      return OTCRYPTO_OK;
    default:
      return OTCRYPTO_BAD_ARGS;
  }
}

/**
 * Compute HMAC-SHA{256,384,512} over `msg1 || msg2 || msg3` using the
 * OTBN masked SHA-2 implementations (`sha256`, `sha384`, `sha512`).
 */
static status_t otbn_hmac_sha2(otcrypto_key_mode_t key_mode, const uint8_t *key,
                               size_t key_len, const uint8_t *msg1,
                               size_t msg1_len, const uint8_t *msg2,
                               size_t msg2_len, const uint8_t *msg3,
                               size_t msg3_len, uint32_t *tag_out) {
  size_t block_bytes = (key_mode == kOtcryptoKeyModeHmacSha256) ? 64 : 128;
  size_t digest_bytes =
      (key_mode == kOtcryptoKeyModeHmacSha256)
          ? 32
          : ((key_mode == kOtcryptoKeyModeHmacSha384) ? 48 : 64);

  uint8_t k_pad[kHkdfMaxBlockBytes];
  memset(k_pad, 0, sizeof(k_pad));
  if (key_len > 0) {
    if (key_len <= block_bytes) {
      memcpy(k_pad, key, key_len);
    } else {
      uint32_t hashed_key[kHkdfMaxDigestWords];
      switch (key_mode) {
        case kOtcryptoKeyModeHmacSha256:
          HARDENED_TRY(sha256(key, key_len, hashed_key));
          break;
        case kOtcryptoKeyModeHmacSha384:
          HARDENED_TRY(sha384(key, key_len, hashed_key));
          break;
        case kOtcryptoKeyModeHmacSha512:
          HARDENED_TRY(sha512(key, key_len, hashed_key));
          break;
        default:
          return OTCRYPTO_BAD_ARGS;
      }
      memcpy(k_pad, hashed_key, digest_bytes);
      HARDENED_TRY(hardened_memshred(hashed_key, kHkdfMaxDigestWords));
    }
  }

  uint8_t k_ipad[kHkdfMaxBlockBytes];
  uint8_t k_opad[kHkdfMaxBlockBytes];
  for (size_t i = 0; i < block_bytes; i++) {
    k_ipad[i] = k_pad[i] ^ 0x36;
    k_opad[i] = k_pad[i] ^ 0x5c;
  }

  uint32_t inner_digest[kHkdfMaxDigestWords];
  switch (key_mode) {
    case kOtcryptoKeyModeHmacSha256: {
      sha256_state_t st;
      HARDENED_TRY(sha256_init(&st));
      HARDENED_TRY(sha256_update(&st, k_ipad, block_bytes));
      if (msg1_len > 0) {
        HARDENED_TRY(sha256_update(&st, msg1, msg1_len));
      }
      if (msg2_len > 0) {
        HARDENED_TRY(sha256_update(&st, msg2, msg2_len));
      }
      if (msg3_len > 0) {
        HARDENED_TRY(sha256_update(&st, msg3, msg3_len));
      }
      HARDENED_TRY(sha256_final(&st, inner_digest));

      HARDENED_TRY(sha256_init(&st));
      HARDENED_TRY(sha256_update(&st, k_opad, block_bytes));
      HARDENED_TRY(
          sha256_update(&st, (const uint8_t *)inner_digest, digest_bytes));
      HARDENED_TRY(sha256_final(&st, tag_out));
      break;
    }
    case kOtcryptoKeyModeHmacSha384: {
      sha384_state_t st;
      HARDENED_TRY(sha384_init(&st));
      HARDENED_TRY(sha384_update(&st, k_ipad, block_bytes));
      if (msg1_len > 0) {
        HARDENED_TRY(sha384_update(&st, msg1, msg1_len));
      }
      if (msg2_len > 0) {
        HARDENED_TRY(sha384_update(&st, msg2, msg2_len));
      }
      if (msg3_len > 0) {
        HARDENED_TRY(sha384_update(&st, msg3, msg3_len));
      }
      HARDENED_TRY(sha384_final(&st, inner_digest));

      HARDENED_TRY(sha384_init(&st));
      HARDENED_TRY(sha384_update(&st, k_opad, block_bytes));
      HARDENED_TRY(
          sha384_update(&st, (const uint8_t *)inner_digest, digest_bytes));
      HARDENED_TRY(sha384_final(&st, tag_out));
      break;
    }
    case kOtcryptoKeyModeHmacSha512: {
      sha512_state_t st;
      HARDENED_TRY(sha512_init(&st));
      HARDENED_TRY(sha512_update(&st, k_ipad, block_bytes));
      if (msg1_len > 0) {
        HARDENED_TRY(sha512_update(&st, msg1, msg1_len));
      }
      if (msg2_len > 0) {
        HARDENED_TRY(sha512_update(&st, msg2, msg2_len));
      }
      if (msg3_len > 0) {
        HARDENED_TRY(sha512_update(&st, msg3, msg3_len));
      }
      HARDENED_TRY(sha512_final(&st, inner_digest));

      HARDENED_TRY(sha512_init(&st));
      HARDENED_TRY(sha512_update(&st, k_opad, block_bytes));
      HARDENED_TRY(
          sha512_update(&st, (const uint8_t *)inner_digest, digest_bytes));
      HARDENED_TRY(sha512_final(&st, tag_out));
      break;
    }
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  HARDENED_TRY(hardened_memshred(inner_digest, kHkdfMaxDigestWords));
  return OTCRYPTO_OK;
}

/**
 * Run the masked OTBN HKDF app (`run_hkdf_sha{256,384,512}`).
 *
 * Keeps `ikm`, `prk`, and `okm` boolean-shared throughout on OTBN.
 */
static status_t hkdf_otbn_run(const hkdf_otbn_app_cfg_t *cfg,
                              const otcrypto_blinded_key_t *ikm,
                              const otcrypto_const_byte_buf_t *salt,
                              const otcrypto_const_byte_buf_t *info,
                              size_t num_okm_blocks,
                              otcrypto_blinded_key_t *prk_out,
                              otcrypto_blinded_key_t *okm_out) {
  uint32_t salt_buf[32];
  memset(salt_buf, 0, sizeof(salt_buf));
  size_t block_bytes = cfg->block_words * sizeof(uint32_t);
  if (salt != NULL && salt->len > 0) {
    if (salt->len <= block_bytes) {
      memcpy(salt_buf, salt->data, salt->len);
    } else {
      switch (ikm->config.key_mode) {
        case kOtcryptoKeyModeHmacSha256:
          HARDENED_TRY(sha256(salt->data, salt->len, salt_buf));
          break;
        case kOtcryptoKeyModeHmacSha384:
          HARDENED_TRY(sha384(salt->data, salt->len, salt_buf));
          break;
        case kOtcryptoKeyModeHmacSha512:
          HARDENED_TRY(sha512(salt->data, salt->len, salt_buf));
          break;
        default:
          return OTCRYPTO_BAD_ARGS;
      }
    }
  }

  switch (launder32(ikm->config.key_mode)) {
    case kOtcryptoKeyModeHmacSha256: {
      const otbn_app_t kApp = OTBN_APP_T_INIT(run_hkdf_sha256);
      HARDENED_TRY(otbn_load_app(kApp));
      break;
    }
    case kOtcryptoKeyModeHmacSha384: {
      const otbn_app_t kApp = OTBN_APP_T_INIT(run_hkdf_sha384);
      HARDENED_TRY(otbn_load_app(kApp));
      break;
    }
    case kOtcryptoKeyModeHmacSha512: {
      const otbn_app_t kApp = OTBN_APP_T_INIT(run_hkdf_sha512);
      HARDENED_TRY(otbn_load_app(kApp));
      break;
    }
    default:
      return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_TRY(otbn_dmem_write(cfg->block_words, salt_buf, cfg->addr_salt));

  uint32_t *ikm_share0;
  uint32_t *ikm_share1;
  HARDENED_TRY(keyblob_to_shares(ikm, &ikm_share0, &ikm_share1));
  size_t ikm_share_words = keyblob_share_num_words(ikm->config);
  uint32_t ikm_s0_buf[32];
  uint32_t ikm_s1_buf[32];
  for (size_t i = 0; i < cfg->ikm_words; i++) {
    uint32_t r = ibex_rnd32_read();
    if (i < ikm_share_words) {
      ikm_s0_buf[i] = ikm_share0[i] ^ r;
      ikm_s1_buf[i] = ikm_share1[i] ^ r;
    } else {
      ikm_s0_buf[i] = r;
      ikm_s1_buf[i] = r;
    }
  }
  HARDENED_TRY(otbn_dmem_write(cfg->ikm_words, ikm_s0_buf, cfg->addr_ikm_s0));
  HARDENED_TRY(otbn_dmem_write(cfg->ikm_words, ikm_s1_buf, cfg->addr_ikm_s1));

  uint32_t ikm_len_u32 = (uint32_t)ikm->config.key_length;
  HARDENED_TRY(otbn_dmem_write(1, &ikm_len_u32, cfg->addr_ikm_len));

  uint32_t info_buf[24];
  memset(info_buf, 0, sizeof(info_buf));
  uint32_t info_len_u32 = 0;
  if (info != NULL && info->len > 0) {
    memcpy(info_buf, info->data, info->len);
    info_len_u32 = (uint32_t)info->len;
  }
  HARDENED_TRY(otbn_dmem_write(24, info_buf, cfg->addr_info));
  HARDENED_TRY(otbn_dmem_write(1, &info_len_u32, cfg->addr_info_len));

  uint32_t num_blocks_u32 = (uint32_t)num_okm_blocks;
  HARDENED_TRY(otbn_dmem_write(1, &num_blocks_u32, cfg->addr_num_okm_blocks));

  HARDENED_TRY(otbn_execute());
  HARDENED_TRY_WIPE_DMEM(otbn_busy_wait_for_done());

  if (prk_out != NULL) {
    uint32_t *prk_share0 = prk_out->keyblob;
    uint32_t *prk_share1 =
        prk_out->keyblob + keyblob_share_num_words(prk_out->config);
    HARDENED_TRY_WIPE_DMEM(
        otbn_dmem_read(cfg->digest_words, cfg->addr_prk_s0, prk_share0));
    HARDENED_TRY_WIPE_DMEM(
        otbn_dmem_read(cfg->digest_words, cfg->addr_prk_s1, prk_share1));
    prk_out->checksum = otcrypto_integrity_blinded_checksum(prk_out);
  }

  if (okm_out != NULL) {
    size_t okm_wordlen = keyblob_share_num_words(okm_out->config);
    uint32_t *okm_share0 = okm_out->keyblob;
    uint32_t *okm_share1 = okm_out->keyblob + okm_wordlen;
    HARDENED_TRY_WIPE_DMEM(
        otbn_dmem_read(okm_wordlen, cfg->addr_okm_s0, okm_share0));
    HARDENED_TRY_WIPE_DMEM(
        otbn_dmem_read(okm_wordlen, cfg->addr_okm_s1, okm_share1));
    okm_out->checksum = otcrypto_integrity_blinded_checksum(okm_out);
  }

  HARDENED_TRY(otbn_dmem_sec_wipe());
  return OTCRYPTO_OK;
}

static status_t hkdf_check_prk(size_t digest_words,
                               const otcrypto_blinded_key_t *prk) {
  if (launder32(prk->config.key_mode) >> 16 != kOtcryptoKeyTypeHmac) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(prk->config.key_mode >> 16, kOtcryptoKeyTypeHmac);

  size_t digest_bytelen = digest_words * sizeof(uint32_t);
  if (launder32(prk->config.key_length) != digest_bytelen) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(prk->config.key_length, digest_bytelen);

  size_t keyblob_bytelen = keyblob_num_words(prk->config) * sizeof(uint32_t);
  if (launder32(prk->keyblob_length) != keyblob_bytelen) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(prk->keyblob_length, keyblob_bytelen);

  return keyblob_ensure_xor_masked(prk->config);
}

otcrypto_status_t otbn_hkdf_extract(const otcrypto_blinded_key_t *ikm,
                                    const otcrypto_const_byte_buf_t *salt,
                                    otcrypto_blinded_key_t *prk) {
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (ikm == NULL || ikm->keyblob == NULL || prk == NULL ||
      prk->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (salt == NULL || (salt->data == NULL && salt->len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  if (launder32(otcrypto_integrity_blinded_key_check(ikm)) !=
      kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (launder32(prk->config.key_mode) != launder32(ikm->config.key_mode)) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(prk->config.key_mode, ikm->config.key_mode);

  hkdf_otbn_app_cfg_t cfg;
  HARDENED_TRY(get_otbn_app_cfg(ikm->config.key_mode, &cfg));
  HARDENED_TRY(hkdf_check_prk(cfg.digest_words, prk));
  HARDENED_TRY(keyblob_ensure_xor_masked(ikm->config));

  if (ikm->config.key_length <= cfg.max_ikm_bytes) {
    HARDENED_TRY(hkdf_otbn_run(&cfg, ikm, salt, NULL, 1, prk, NULL));
    return otcrypto_eval_exit(OTCRYPTO_OK);
  }

  // Fallback for oversized IKM (> 64B for SHA-256 or > 111B for SHA-384/512):
  // compute HMAC using OTBN masked SHA-2 (`run_sha{256,384,512}`).
  size_t unmasked_ikm_wordlen = keyblob_share_num_words(ikm->config);
  if (unmasked_ikm_wordlen > kHkdfMaxIkmWords) {
    return OTCRYPTO_BAD_ARGS;
  }
  uint32_t unmasked_ikm[kHkdfMaxIkmWords];
  HARDENED_TRY(keyblob_key_unmask(ikm, unmasked_ikm_wordlen, unmasked_ikm));

  uint32_t tag_data[kHkdfMaxDigestWords];
  HARDENED_TRY(otbn_hmac_sha2(ikm->config.key_mode, salt->data, salt->len,
                              (const uint8_t *)unmasked_ikm,
                              ikm->config.key_length, NULL, 0, NULL, 0,
                              tag_data));

  uint32_t prk_mask[kHkdfMaxDigestWords];
  HARDENED_TRY(hardened_memshred(prk_mask, cfg.digest_words));
  HARDENED_TRY(
      keyblob_from_key_and_mask(tag_data, prk_mask, prk->config, prk->keyblob));

  HARDENED_TRY(hardened_memshred(unmasked_ikm, unmasked_ikm_wordlen));
  HARDENED_TRY(hardened_memshred(tag_data, cfg.digest_words));

  prk->checksum = otcrypto_integrity_blinded_checksum(prk);
  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otbn_hkdf_expand(const otcrypto_blinded_key_t *prk,
                                   const otcrypto_const_byte_buf_t *info,
                                   otcrypto_blinded_key_t *okm) {
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (okm == NULL || okm->keyblob == NULL || prk == NULL ||
      prk->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (info == NULL || (info->data == NULL && info->len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  if (launder32(otcrypto_integrity_blinded_key_check(prk)) !=
      kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }

  hkdf_otbn_app_cfg_t cfg;
  HARDENED_TRY(get_otbn_app_cfg(prk->config.key_mode, &cfg));
  HARDENED_TRY(hkdf_check_prk(cfg.digest_words, prk));
  HARDENED_TRY(keyblob_ensure_xor_masked(okm->config));

  size_t keyblob_bytelen = keyblob_num_words(okm->config) * sizeof(uint32_t);
  if (launder32(okm->keyblob_length) != keyblob_bytelen) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(okm->keyblob_length, keyblob_bytelen);

  size_t okm_bytelen = okm->config.key_length;
  size_t okm_wordlen = ceil_div(okm_bytelen, sizeof(uint32_t));
  size_t num_iterations = ceil_div(okm_wordlen, cfg.digest_words);
  if (launder32(num_iterations) > 255) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_LE(num_iterations, 255);

  uint32_t unmasked_prk[kHkdfMaxDigestWords];
  HARDENED_TRY(keyblob_key_unmask(prk, cfg.digest_words, unmasked_prk));
  size_t digest_bytes = cfg.digest_words * sizeof(uint32_t);

  uint32_t *share0_ptr = okm->keyblob;
  uint32_t *share1_ptr = okm->keyblob + keyblob_share_num_words(okm->config);
  size_t words_written = 0;
  uint32_t prev_t[kHkdfMaxDigestWords];

  for (uint8_t i = 0; i < num_iterations; i++) {
    uint8_t counter_val = i + 1;
    uint32_t tag_data[kHkdfMaxDigestWords];
    HARDENED_TRY(otbn_hmac_sha2(
        prk->config.key_mode, (const uint8_t *)unmasked_prk, digest_bytes,
        (i == 0) ? NULL : (const uint8_t *)prev_t, (i == 0) ? 0 : digest_bytes,
        info->data, info->len, &counter_val, 1, tag_data));

    memcpy(prev_t, tag_data, digest_bytes);

    size_t words_to_copy = cfg.digest_words;
    if (words_written + cfg.digest_words > okm_wordlen) {
      words_to_copy = okm_wordlen - words_written;
    }

    uint32_t mask_data[kHkdfMaxDigestWords];
    HARDENED_TRY(hardened_memshred(mask_data, words_to_copy));

    uint32_t share0_data[kHkdfMaxDigestWords];
    HARDENED_TRY(hardened_xor(tag_data, mask_data, words_to_copy, share0_data));

    HARDENED_TRY(hardened_memcpy(share0_ptr + words_written, share0_data,
                                 words_to_copy));
    HARDENED_TRY(
        hardened_memcpy(share1_ptr + words_written, mask_data, words_to_copy));

    words_written += words_to_copy;
  }

  HARDENED_TRY(hardened_memshred(unmasked_prk, cfg.digest_words));
  HARDENED_TRY(hardened_memshred(prev_t, cfg.digest_words));

  okm->checksum = otcrypto_integrity_blinded_checksum(okm);
  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otbn_hkdf(const otcrypto_blinded_key_t *ikm,
                            const otcrypto_const_byte_buf_t *salt,
                            const otcrypto_const_byte_buf_t *info,
                            otcrypto_blinded_key_t *okm) {
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (ikm == NULL || ikm->keyblob == NULL || okm == NULL ||
      okm->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (salt == NULL || (salt->data == NULL && salt->len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (info == NULL || (info->data == NULL && info->len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  if (launder32(otcrypto_integrity_blinded_key_check(ikm)) !=
      kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }

  hkdf_otbn_app_cfg_t cfg;
  HARDENED_TRY(get_otbn_app_cfg(ikm->config.key_mode, &cfg));
  HARDENED_TRY(keyblob_ensure_xor_masked(ikm->config));
  HARDENED_TRY(keyblob_ensure_xor_masked(okm->config));

  size_t okm_keyblob_bytelen =
      keyblob_num_words(okm->config) * sizeof(uint32_t);
  if (launder32(okm->keyblob_length) != okm_keyblob_bytelen) {
    return OTCRYPTO_BAD_ARGS;
  }

  size_t okm_bytelen = okm->config.key_length;
  size_t okm_wordlen = ceil_div(okm_bytelen, sizeof(uint32_t));
  size_t num_iterations = ceil_div(okm_wordlen, cfg.digest_words);
  if (launder32(num_iterations) > 255) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Use the single-shot masked OTBN HKDF binary when inputs fit OTBN buffers.
  if (ikm->config.key_length <= cfg.max_ikm_bytes &&
      info->len <= cfg.max_info_bytes && num_iterations >= 1 &&
      num_iterations <= cfg.max_okm_blocks) {
    HARDENED_TRY(
        hkdf_otbn_run(&cfg, ikm, salt, info, num_iterations, NULL, okm));
    return otcrypto_eval_exit(OTCRYPTO_OK);
  }

  size_t digest_bytelen = cfg.digest_words * sizeof(uint32_t);
  otcrypto_key_config_t prk_config = {
      .version = otcrypto_lib_version(),
      .key_mode = ikm->config.key_mode,
      .key_length = digest_bytelen,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  size_t keyblob_wordlen = keyblob_num_words(prk_config);
  uint32_t keyblob[kHkdfMaxDigestWords * 2];
  otcrypto_blinded_key_t prk = {
      .config = prk_config,
      .keyblob = keyblob,
      .keyblob_length = keyblob_wordlen * sizeof(uint32_t),
  };

  HARDENED_TRY(otbn_hkdf_extract(ikm, salt, &prk));
  return otbn_hkdf_expand(&prk, info, okm);
}
