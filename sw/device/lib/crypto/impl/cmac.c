// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/cmac.h"

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/aes.h"
#include "sw/device/lib/crypto/drivers/keymgr.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/integrity.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('c', 'm', 'c')

/**
 * Internal CMAC context.
 */
typedef struct {
  uint32_t key_share0[8];
  uint32_t key_share1[8];
  uint32_t key_len_words;
  hardened_bool_t sideload;
  aes_block_t k1;
  aes_block_t k2;
  aes_block_t iv;
  uint32_t partial_block[4];
  uint32_t partial_block_len;
} cmac_ctx_t;

/**
 * Ensure that the CMAC context is large enough. For FI hardening, two redundant
 * contexts are created as well as a word storing the security level.
 */
static_assert(
    sizeof(otcrypto_cmac_context_t) >=
        2 * sizeof(cmac_ctx_t) + sizeof(uint32_t),
    "`otcrypto_cmac_context_t` must hold two `cmac_ctx_t` plus a word.");

/**
 * Ensure that CMAC driver struct is a multiple of the word size.
 */
static_assert(sizeof(cmac_ctx_t) % sizeof(uint32_t) == 0,
              "Size of `cmac_ctx_t` must be a multiple of the word size");

/**
 * Define the number of words in the internal context struct.
 */
#define kOtcryptoCmacCtxStructWords (sizeof(cmac_ctx_t) / sizeof(uint32_t))

enum {
  // Slot 0: security level (otcrypto_key_security_level_t cast to uint32_t).
  kCtxSecurityLevelOffset = 0,
  // Slot 1: primary cmac_ctx_t.
  kCtxPrimaryOffset = 1,
  // Slot 2: redundant cmac_ctx_t (medium/high security only).
  kCtxRedundantOffset = 1 + kOtcryptoCmacCtxStructWords,
};

/**
 * AES cleanup guard.
 */
static void aes_wipe_guard(uint32_t *dummy) { (void)aes_clear(); }

/**
 * Sideload cleanup guard.
 */
static void sideload_wipe_guard(hardened_bool_t *is_sideloaded) {
  if (*is_sideloaded == kHardenedBoolTrue) {
    (void)keymgr_sideload_clear_aes();
  }
}

/**
 * Checks for NULL pointers or invalid settings in the blinded key.
 */
static status_t check_key(const otcrypto_blinded_key_t *key) {
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (key == NULL || key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif
  // Check the integrity of the key.
  if (launder32(otcrypto_integrity_blinded_key_check(key)) !=
      kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(otcrypto_integrity_blinded_key_check(key),
                    kHardenedBoolTrue);
  return OTCRYPTO_OK;
}

/**
 * Prepares an `aes_key_t` structure from the internal context.
 */
static status_t build_aes_key(const cmac_ctx_t *ctx, aes_key_t *aes_key) {
  aes_key->mode = kAesCipherModeCbc;
  aes_key->sideload = ctx->sideload;
  aes_key->key_len = ctx->key_len_words;
  if (launder32(ctx->sideload) == kHardenedBoolTrue) {
    HARDENED_CHECK_EQ(ctx->sideload, kHardenedBoolTrue);
    aes_key->key_shares[0] = NULL;
    aes_key->key_shares[1] = NULL;
  } else if (launder32(ctx->sideload) == kHardenedBoolFalse) {
    HARDENED_CHECK_EQ(ctx->sideload, kHardenedBoolFalse);
    aes_key->key_shares[0] = (uint32_t *)ctx->key_share0;
    aes_key->key_shares[1] = (uint32_t *)ctx->key_share1;
  } else {
    return OTCRYPTO_BAD_ARGS;
  }
  aes_key->checksum = aes_key_integrity_checksum(aes_key);
  return OTCRYPTO_OK;
}

/**
 * Copies the key shares into the internal context to persist them.
 */
static status_t cmac_key_construct(const otcrypto_blinded_key_t *key,
                                   cmac_ctx_t *ctx) {
  ctx->sideload = key->config.hw_backed;
  ctx->key_len_words = keyblob_share_num_words(key->config);

  if (launder32(ctx->sideload) == kHardenedBoolTrue) {
    HARDENED_CHECK_EQ(ctx->sideload, kHardenedBoolTrue);
    HARDENED_TRY(
        hardened_memshred(ctx->key_share0, ARRAYSIZE(ctx->key_share0)));
    HARDENED_TRY(
        hardened_memshred(ctx->key_share1, ARRAYSIZE(ctx->key_share1)));
  } else if (launder32(ctx->sideload) == kHardenedBoolFalse) {
    HARDENED_CHECK_EQ(ctx->sideload, kHardenedBoolFalse);
    uint32_t *share0;
    uint32_t *share1;
    HARDENED_TRY(keyblob_to_shares(key, &share0, &share1));
    HARDENED_TRY(hardened_memcpy(ctx->key_share0, share0, ctx->key_len_words));
    HARDENED_TRY(hardened_memcpy(ctx->key_share1, share1, ctx->key_len_words));
  } else {
    return OTCRYPTO_BAD_ARGS;
  }
  return OTCRYPTO_OK;
}

/**
 * Subkey generation per NIST SP 800-38B.
 */
static status_t generate_subkey(const aes_block_t *in, aes_block_t *out) {
  uint32_t in_buf[kAesBlockNumWords];
  uint32_t out_buf[kAesBlockNumWords];

  HARDENED_TRY(hardened_memcpy(in_buf, in->data, kAesBlockNumWords));

  uint8_t *in_bytes = (uint8_t *)in_buf;
  uint8_t *out_bytes = (uint8_t *)out_buf;

  uint8_t msb = in_bytes[0] >> 7;
  size_t i;
  for (i = 0; launder32(i) < kAesBlockNumBytes - 1; ++i) {
    out_bytes[i] = (uint8_t)((in_bytes[i] << 1) | (in_bytes[i + 1] >> 7));
  }
  HARDENED_CHECK_EQ(i, kAesBlockNumBytes - 1);

  out_bytes[kAesBlockNumBytes - 1] =
      (uint8_t)(in_bytes[kAesBlockNumBytes - 1] << 1) ^
      ((uint8_t)(-(int8_t)msb) & 0x87);

  HARDENED_TRY(hardened_memcpy(out->data, out_buf, kAesBlockNumWords));
  return OTCRYPTO_OK;
}

/**
 * Core init operation.
 */
static status_t cmac_init_core(cmac_ctx_t *ctx) {
  aes_key_t aes_key;
  HARDENED_TRY(build_aes_key(ctx, &aes_key));

  aes_block_t zero_iv = {0};
  aes_block_t zero_block = {0};
  aes_block_t L;

  HARDENED_TRY(aes_encrypt_begin(aes_key, &zero_iv));
  HARDENED_TRY(aes_update(NULL, &zero_block));
  HARDENED_TRY(aes_update(&L, NULL));
  HARDENED_TRY(aes_end(NULL));

  HARDENED_TRY(generate_subkey(&L, &ctx->k1));
  HARDENED_TRY(generate_subkey(&ctx->k1, &ctx->k2));

  HARDENED_TRY(hardened_memshred(L.data, ARRAYSIZE(L.data)));

  size_t i;
  uint32_t *iv_words = ctx->iv.data;
  for (i = 0; launder32(i) < kAesBlockNumWords; ++i) {
    iv_words[i] = 0;
  }
  HARDENED_CHECK_EQ(i, kAesBlockNumWords);
  ctx->partial_block_len = 0;

  return OTCRYPTO_OK;
}

/**
 * Core update operation.
 */
static status_t cmac_update_core(
    cmac_ctx_t *ctx, const otcrypto_const_byte_buf_t *input_message) {
  if (input_message->len == 0) {
    return OTCRYPTO_OK;
  }

  aes_key_t aes_key;
  HARDENED_TRY(build_aes_key(ctx, &aes_key));
  HARDENED_TRY(aes_encrypt_begin(aes_key, &ctx->iv));

  size_t offset = 0;
  uint8_t *partial_bytes = (uint8_t *)ctx->partial_block;

  if (launder32(ctx->partial_block_len) > 0 &&
      (launder32(ctx->partial_block_len + input_message->len) >
       kAesBlockNumBytes)) {
    HARDENED_CHECK_GT(ctx->partial_block_len, 0);
    HARDENED_CHECK_GT(ctx->partial_block_len + input_message->len,
                      kAesBlockNumBytes);

    size_t copy_len = kAesBlockNumBytes - ctx->partial_block_len;
    HARDENED_TRY(randomized_bytecopy(partial_bytes + ctx->partial_block_len,
                                     input_message->data, copy_len));

    aes_block_t block_in, block_out;
    HARDENED_TRY(
        hardened_memcpy(block_in.data, ctx->partial_block, kAesBlockNumWords));

    HARDENED_TRY(aes_update(NULL, &block_in));
    HARDENED_TRY(aes_update(&block_out, NULL));

    ctx->partial_block_len = 0;
    offset += copy_len;
  }

  // Ensure input_message->len is not smaller than offset to prevent underflow
  if (launder32(input_message->len) < launder32(offset)) {
    return OTCRYPTO_FATAL_ERR;
  }
  HARDENED_CHECK_GE(input_message->len, offset);

  while (launder32(input_message->len - offset) > kAesBlockNumBytes) {
    HARDENED_CHECK_GT(input_message->len - offset, kAesBlockNumBytes);
    aes_block_t block_in, block_out;

    HARDENED_TRY(randomized_bytecopy((uint8_t *)block_in.data,
                                     input_message->data + offset,
                                     kAesBlockNumBytes));

    HARDENED_TRY(aes_update(NULL, &block_in));
    HARDENED_TRY(aes_update(&block_out, NULL));
    offset += kAesBlockNumBytes;
  }

  size_t remaining = input_message->len - offset;
  if (launder32(remaining) > 0) {
    HARDENED_CHECK_GT(remaining, 0);
    HARDENED_TRY(randomized_bytecopy(partial_bytes + ctx->partial_block_len,
                                     input_message->data + offset, remaining));
    ctx->partial_block_len += remaining;
  }

  HARDENED_TRY(aes_end(&ctx->iv));
  return OTCRYPTO_OK;
}

/**
 * Core final operation.
 */
static status_t cmac_final_core(cmac_ctx_t *ctx, otcrypto_word32_buf_t *tag) {
  aes_key_t aes_key;
  HARDENED_TRY(build_aes_key(ctx, &aes_key));
  HARDENED_TRY(aes_encrypt_begin(aes_key, &ctx->iv));

  aes_block_t block_in, block_out;

  uint32_t final_block_words[kAesBlockNumWords];
  uint8_t *final_block = (uint8_t *)final_block_words;
  uint8_t *partial_bytes = (uint8_t *)ctx->partial_block;

  if (launder32(ctx->partial_block_len) == kAesBlockNumBytes) {
    HARDENED_CHECK_EQ(ctx->partial_block_len, kAesBlockNumBytes);
    HARDENED_TRY(hardened_memcpy(final_block_words, ctx->partial_block,
                                 kAesBlockNumWords));

    size_t i;
    for (i = 0; launder32(i) < kAesBlockNumBytes; i++) {
      final_block[i] ^= ((uint8_t *)ctx->k1.data)[i];
    }
    HARDENED_CHECK_EQ(i, kAesBlockNumBytes);
  } else {
    HARDENED_CHECK_LT(ctx->partial_block_len, kAesBlockNumBytes);
    HARDENED_TRY(randomized_bytecopy(final_block, partial_bytes,
                                     ctx->partial_block_len));

    final_block[ctx->partial_block_len] = 0x80;
    size_t padding_len = kAesBlockNumBytes - ctx->partial_block_len - 1;

    if (launder32(padding_len) > 0) {
      HARDENED_CHECK_GT(padding_len, 0);
      size_t i;
      for (i = 0; launder32(i) < padding_len; i++) {
        final_block[ctx->partial_block_len + 1 + i] = 0x00;
      }
      HARDENED_CHECK_EQ(i, padding_len);
    }

    size_t i;
    for (i = 0; launder32(i) < kAesBlockNumBytes; i++) {
      final_block[i] ^= ((uint8_t *)ctx->k2.data)[i];
    }
    HARDENED_CHECK_EQ(i, kAesBlockNumBytes);
  }

  HARDENED_TRY(
      hardened_memcpy(block_in.data, final_block_words, kAesBlockNumWords));
  HARDENED_TRY(aes_update(NULL, &block_in));
  HARDENED_TRY(aes_update(&block_out, NULL));
  HARDENED_TRY(aes_end(&ctx->iv));

  size_t copy_words = tag->len;
  if (launder32(copy_words) > kAesBlockNumWords) {
    copy_words = kAesBlockNumWords;
  }
  HARDENED_CHECK_LE(copy_words, kAesBlockNumWords);
  HARDENED_TRY(hardened_memcpy(tag->data, block_out.data, copy_words));

  return OTCRYPTO_OK;
}

OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_cmac(const otcrypto_blinded_key_t *key,
                                const otcrypto_const_byte_buf_t *input_message,
                                otcrypto_word32_buf_t *tag) {
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (tag == NULL || tag->data == NULL || input_message == NULL ||
      (input_message->data == NULL && input_message->len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  // Clear AES unconditionally, and clear sideload if requested.
  uint32_t hw_cleanup_guard __attribute__((cleanup(aes_wipe_guard))) = 1;
  (void)hw_cleanup_guard;
  hardened_bool_t is_sideloaded __attribute__((cleanup(sideload_wipe_guard))) =
      kHardenedBoolFalse;

  HARDENED_TRY(hardened_memshred(tag->data, tag->len));
  HARDENED_TRY(check_key(key));

  if (launder32(key->config.hw_backed) == kHardenedBoolTrue) {
    HARDENED_CHECK_EQ(key->config.hw_backed, kHardenedBoolTrue);
    is_sideloaded = kHardenedBoolTrue;
    keymgr_diversification_t diversification;
    HARDENED_TRY(keyblob_to_keymgr_diversification(key, &diversification));
    HARDENED_TRY(keymgr_generate_key_aes(diversification));
  }

  cmac_ctx_t primary_ctx;
  HARDENED_TRY(cmac_key_construct(key, &primary_ctx));

  if (launder32(key->config.security_level) == kOtcryptoKeySecurityLevelLow) {
    HARDENED_CHECK_EQ(launder32(key->config.security_level),
                      kOtcryptoKeySecurityLevelLow);
    HARDENED_TRY(cmac_init_core(&primary_ctx));
    HARDENED_TRY(cmac_update_core(&primary_ctx, input_message));
    return otcrypto_eval_exit(cmac_final_core(&primary_ctx, tag));

  } else if (launder32(key->config.security_level) ==
             kOtcryptoKeySecurityLevelMedium) {
    HARDENED_CHECK_EQ(launder32(key->config.security_level),
                      kOtcryptoKeySecurityLevelMedium);

    // First invocation
    HARDENED_TRY(cmac_init_core(&primary_ctx));
    HARDENED_TRY(cmac_update_core(&primary_ctx, input_message));
    HARDENED_TRY(cmac_final_core(&primary_ctx, tag));

    // Redundant invocation
    uint32_t tag_redundant_data[kAesBlockNumWords];
    otcrypto_word32_buf_t tag_redundant =
        OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, tag_redundant_data, tag->len);
    cmac_ctx_t redundant_ctx;
    HARDENED_TRY(cmac_key_construct(key, &redundant_ctx));
    HARDENED_TRY(cmac_init_core(&redundant_ctx));
    HARDENED_TRY(cmac_update_core(&redundant_ctx, input_message));
    HARDENED_TRY(cmac_final_core(&redundant_ctx, &tag_redundant));

    HARDENED_CHECK_EQ(
        hardened_memeq(&tag->data[0], &tag_redundant.data[0], tag->len),
        kHardenedBoolTrue);
    return otcrypto_eval_exit(OTCRYPTO_OK);

  } else {
    HARDENED_CHECK_EQ(launder32(key->config.security_level),
                      kOtcryptoKeySecurityLevelHigh);

    // First invocation
    HARDENED_TRY(cmac_init_core(&primary_ctx));
    HARDENED_TRY(cmac_update_core(&primary_ctx, input_message));
    HARDENED_TRY(cmac_final_core(&primary_ctx, tag));

    // Redundant invocation
    uint32_t tag_redundant_data[kAesBlockNumWords];
    otcrypto_word32_buf_t tag_redundant =
        OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, tag_redundant_data, tag->len);
    cmac_ctx_t redundant_ctx;
    HARDENED_TRY(cmac_key_construct(key, &redundant_ctx));
    HARDENED_TRY(cmac_init_core(&redundant_ctx));
    HARDENED_TRY(cmac_update_core(&redundant_ctx, input_message));
    HARDENED_TRY(cmac_final_core(&redundant_ctx, &tag_redundant));

    HARDENED_CHECK_EQ(
        hardened_memeq(&tag->data[0], &tag_redundant.data[0], tag->len),
        kHardenedBoolTrue);
    return otcrypto_eval_exit(OTCRYPTO_OK);
  }

  HARDENED_TRAP();
  return otcrypto_eval_exit(OTCRYPTO_FATAL_ERR);
}

otcrypto_status_t otcrypto_cmac_init(otcrypto_cmac_context_t *ctx,
                                     const otcrypto_blinded_key_t *key) {
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (ctx == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  uint32_t hw_cleanup_guard __attribute__((cleanup(aes_wipe_guard))) = 1;
  (void)hw_cleanup_guard;

  HARDENED_TRY(check_key(key));

  if (launder32(key->config.hw_backed) == kHardenedBoolTrue) {
    HARDENED_CHECK_EQ(key->config.hw_backed, kHardenedBoolTrue);
    keymgr_diversification_t diversification;
    HARDENED_TRY(keyblob_to_keymgr_diversification(key, &diversification));
    HARDENED_TRY(keymgr_generate_key_aes(diversification));
  }

  cmac_ctx_t primary_ctx;
  cmac_ctx_t redundant_ctx;

  HARDENED_TRY(cmac_key_construct(key, &primary_ctx));
  HARDENED_TRY(cmac_init_core(&primary_ctx));

  if (launder32(key->config.security_level) == kOtcryptoKeySecurityLevelLow) {
    HARDENED_CHECK_EQ(launder32(key->config.security_level),
                      kOtcryptoKeySecurityLevelLow);
  } else if (launder32(key->config.security_level) ==
             kOtcryptoKeySecurityLevelMedium) {
    HARDENED_CHECK_EQ(launder32(key->config.security_level),
                      kOtcryptoKeySecurityLevelMedium);
    HARDENED_TRY(cmac_key_construct(key, &redundant_ctx));
    HARDENED_TRY(cmac_init_core(&redundant_ctx));
  } else {
    HARDENED_CHECK_EQ(launder32(key->config.security_level),
                      kOtcryptoKeySecurityLevelHigh);
    HARDENED_TRY(cmac_key_construct(key, &redundant_ctx));
    HARDENED_TRY(cmac_init_core(&redundant_ctx));
  }

  ctx->data[kCtxSecurityLevelOffset] = (uint32_t)key->config.security_level;
  HARDENED_TRY(randomized_bytecopy((uint8_t *)&ctx->data[kCtxPrimaryOffset],
                                   (uint8_t *)&primary_ctx,
                                   sizeof(cmac_ctx_t)));
  HARDENED_CHECK_EQ(
      consttime_memeq_byte(&primary_ctx, &ctx->data[kCtxPrimaryOffset],
                           sizeof(cmac_ctx_t)),
      kHardenedBoolTrue);

  if (launder32(key->config.security_level) != kOtcryptoKeySecurityLevelLow) {
    HARDENED_TRY(randomized_bytecopy((uint8_t *)&ctx->data[kCtxRedundantOffset],
                                     (uint8_t *)&redundant_ctx,
                                     sizeof(cmac_ctx_t)));
    HARDENED_CHECK_EQ(
        consttime_memeq_byte(&redundant_ctx, &ctx->data[kCtxRedundantOffset],
                             sizeof(cmac_ctx_t)),
        kHardenedBoolTrue);
  }
  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_cmac_update(
    otcrypto_cmac_context_t *const ctx,
    const otcrypto_const_byte_buf_t *input_message) {
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (ctx == NULL || input_message == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (input_message->data == NULL && input_message->len != 0) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  uint32_t hw_cleanup_guard __attribute__((cleanup(aes_wipe_guard))) = 1;
  (void)hw_cleanup_guard;

  otcrypto_key_security_level_t security_level =
      (otcrypto_key_security_level_t)ctx->data[kCtxSecurityLevelOffset];

  cmac_ctx_t primary_ctx;
  HARDENED_TRY(hardened_memcpy((uint32_t *)&primary_ctx,
                               (const uint32_t *)&ctx->data[kCtxPrimaryOffset],
                               kOtcryptoCmacCtxStructWords));

  HARDENED_TRY(cmac_update_core(&primary_ctx, input_message));

  HARDENED_TRY(randomized_bytecopy((uint8_t *)&ctx->data[kCtxPrimaryOffset],
                                   (uint8_t *)&primary_ctx,
                                   sizeof(cmac_ctx_t)));
  HARDENED_CHECK_EQ(
      consttime_memeq_byte(&primary_ctx, &ctx->data[kCtxPrimaryOffset],
                           sizeof(cmac_ctx_t)),
      kHardenedBoolTrue);

  if (launder32(security_level) != kOtcryptoKeySecurityLevelLow) {
    cmac_ctx_t redundant_ctx;
    HARDENED_TRY(
        hardened_memcpy((uint32_t *)&redundant_ctx,
                        (const uint32_t *)&ctx->data[kCtxRedundantOffset],
                        kOtcryptoCmacCtxStructWords));

    HARDENED_TRY(cmac_update_core(&redundant_ctx, input_message));

    HARDENED_TRY(randomized_bytecopy((uint8_t *)&ctx->data[kCtxRedundantOffset],
                                     (uint8_t *)&redundant_ctx,
                                     sizeof(cmac_ctx_t)));
    HARDENED_CHECK_EQ(
        consttime_memeq_byte(&redundant_ctx, &ctx->data[kCtxRedundantOffset],
                             sizeof(cmac_ctx_t)),
        kHardenedBoolTrue);
  }

  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_cmac_final(otcrypto_cmac_context_t *const ctx,
                                      otcrypto_word32_buf_t *tag) {
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (ctx == NULL || tag == NULL || tag->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  uint32_t hw_cleanup_guard __attribute__((cleanup(aes_wipe_guard))) = 1;
  (void)hw_cleanup_guard;
  hardened_bool_t is_sideloaded __attribute__((cleanup(sideload_wipe_guard))) =
      kHardenedBoolFalse;

  otcrypto_key_security_level_t security_level =
      (otcrypto_key_security_level_t)ctx->data[kCtxSecurityLevelOffset];

  cmac_ctx_t primary_ctx;
  HARDENED_TRY(hardened_memcpy((uint32_t *)&primary_ctx,
                               (const uint32_t *)&ctx->data[kCtxPrimaryOffset],
                               kOtcryptoCmacCtxStructWords));

  if (launder32(primary_ctx.sideload) == kHardenedBoolTrue) {
    is_sideloaded = kHardenedBoolTrue;
  }

  if (launder32(security_level) == kOtcryptoKeySecurityLevelLow) {
    HARDENED_CHECK_EQ(launder32(security_level), kOtcryptoKeySecurityLevelLow);
    return otcrypto_eval_exit(cmac_final_core(&primary_ctx, tag));
  }

  HARDENED_TRY(cmac_final_core(&primary_ctx, tag));

  cmac_ctx_t redundant_ctx;
  HARDENED_TRY(
      hardened_memcpy((uint32_t *)&redundant_ctx,
                      (const uint32_t *)&ctx->data[kCtxRedundantOffset],
                      kOtcryptoCmacCtxStructWords));

  uint32_t tag_redundant_data[kAesBlockNumWords];
  otcrypto_word32_buf_t tag_redundant =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, tag_redundant_data, tag->len);

  if (launder32(security_level) == kOtcryptoKeySecurityLevelMedium) {
    HARDENED_CHECK_EQ(launder32(security_level),
                      kOtcryptoKeySecurityLevelMedium);
    HARDENED_TRY(cmac_final_core(&redundant_ctx, &tag_redundant));
  } else {
    HARDENED_CHECK_EQ(launder32(security_level), kOtcryptoKeySecurityLevelHigh);
    HARDENED_TRY(cmac_final_core(&redundant_ctx, &tag_redundant));
  }

  HARDENED_CHECK_EQ(hardened_memeq(tag->data, tag_redundant.data, tag->len),
                    kHardenedBoolTrue);
  return otcrypto_eval_exit(OTCRYPTO_OK);
}
