// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/hmac.h"

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/hmac.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/status.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('h', 'm', 'c')

/**
 * Ensure that the HMAC context is large enough for HMAC driver struct.
 */
static_assert(
    sizeof(otcrypto_hmac_context_t) >= sizeof(hmac_ctx_t),
    "`otcrypto_hmac_context_t` must be big enough to hold `hmac_ctx_t`.");

/**
 * Ensure that HMAC driver struct is suitable for `hardened_memcpy()`.
 */
static_assert(sizeof(hmac_ctx_t) % sizeof(uint32_t) == 0,
              "Size of `hmac_ctx_t` must be a multiple of the word size for "
              "`hardened_memcpy()`");

/**
 * Compute the key block (see FIPS 198-1, Section 4, Steps 1-3).
 *
 * Adds padding and in some cases pre-hashes the HMAC key to get a value the
 * length of the underlying message block size.
 *
 * The caller must ensure that at least `key_block_wordlen` 32-bit words of
 * space is allocated at the destination `key_block` buffer.
 *
 * @param key The blinded input key.
 * @param key_block_wordlen Block size in 32-bit words.
 * @param[out] key_block Destination buffer for the key block.
 * @return Result of the operation.
 */
static status_t key_block_get(const otcrypto_blinded_key_t *key,
                              size_t key_block_wordlen, uint32_t *key_block) {
  // HMAC HWIP does not support masking, so we need to unmask the key.
  size_t unmasked_key_len = keyblob_share_num_words(key->config);
  uint32_t unmasked_key[unmasked_key_len];
  HARDENED_TRY(keyblob_key_unmask(key, unmasked_key_len, unmasked_key));

  // Pre-populate with 0s, in order to pad keys smaller than the internal
  // block size, according to FIPS 198-1, Section 4.
  memset(key_block, 0, key_block_wordlen * sizeof(uint32_t));
  // If the key is larger than the internal block size, we need to hash it
  // according to FIPS 198-1, Section 4, Step 2.
  if (launder32(key->config.key_length) >
      key_block_wordlen * sizeof(uint32_t)) {
    switch (key->config.key_mode) {
      case kOtcryptoKeyModeHmacSha256:
        return hmac_hash_sha256((unsigned char *)unmasked_key,
                                key->config.key_length, key_block);
      case kOtcryptoKeyModeHmacSha384:
        return hmac_hash_sha384((unsigned char *)unmasked_key,
                                key->config.key_length, key_block);
      case kOtcryptoKeyModeHmacSha512:
        return hmac_hash_sha512((unsigned char *)unmasked_key,
                                key->config.key_length, key_block);
      default:
        return OTCRYPTO_BAD_ARGS;
    }
    // Should be unreachable.
    HARDENED_TRAP();
    return OTCRYPTO_FATAL_ERR;
  } else {
    HARDENED_CHECK_LE(key->config.key_length,
                      key_block_wordlen * sizeof(uint32_t));
    hardened_memcpy(key_block, unmasked_key, unmasked_key_len);
    // If the key size isn't a multiple of the word size, zero the last few
    // bytes.
    size_t offset = key->config.key_length % sizeof(uint32_t);
    if (offset != 0) {
      unsigned char *key_end_ptr =
          (unsigned char *)(&key_block[unmasked_key_len]);
      size_t num_zero_bytes = sizeof(uint32_t) - offset;
      memset(key_end_ptr - num_zero_bytes, 0, num_zero_bytes);
    }
  }

  return OTCRYPTO_OK;
}

/**
 * Checks for NULL pointers or invalid settings in the HMAC key.
 *
 * @param key HMAC key.
 * @return OK or error.
 */
static status_t check_key(const otcrypto_blinded_key_t *key) {
  if (key == NULL || key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // The underlying HMAC hardware is unmasked, and does not have sideload
  // support.
  if (key->config.hw_backed != kHardenedBoolFalse ||
      key->config.security_level != kOtcryptoKeySecurityLevelLow) {
    return OTCRYPTO_NOT_IMPLEMENTED;
  }

  // Check the integrity of the key.
  if (launder32(integrity_blinded_key_check(key)) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(integrity_blinded_key_check(key), kHardenedBoolTrue);

  return OTCRYPTO_OK;
}

OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_hmac(const otcrypto_blinded_key_t *key,
                                otcrypto_const_byte_buf_t input_message,
                                otcrypto_word32_buf_t tag) {
  // Check for null pointers.
  if (tag.data == NULL ||
      (input_message.data == NULL && input_message.len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the key for null pointers or invalid configurations.
  HARDENED_TRY(check_key(key));

  // Call the appropriate function from the HMAC driver.
  switch (launder32(key->config.key_mode)) {
    case kOtcryptoKeyModeHmacSha256: {
      HARDENED_CHECK_EQ(key->config.key_mode, kOtcryptoKeyModeHmacSha256);
      uint32_t key_block[kHmacSha256BlockWords];
      HARDENED_TRY(key_block_get(key, ARRAYSIZE(key_block), key_block));
      return hmac_hmac_sha256(key_block, input_message.data, input_message.len,
                              tag.data);
    }
    case kOtcryptoKeyModeHmacSha384: {
      HARDENED_CHECK_EQ(key->config.key_mode, kOtcryptoKeyModeHmacSha384);
      uint32_t key_block[kHmacSha384BlockWords];
      HARDENED_TRY(key_block_get(key, ARRAYSIZE(key_block), key_block));
      return hmac_hmac_sha384(key_block, input_message.data, input_message.len,
                              tag.data);
    }
    case kOtcryptoKeyModeHmacSha512: {
      HARDENED_CHECK_EQ(key->config.key_mode, kOtcryptoKeyModeHmacSha512);
      uint32_t key_block[kHmacSha512BlockWords];
      HARDENED_TRY(key_block_get(key, ARRAYSIZE(key_block), key_block));
      return hmac_hmac_sha512(key_block, input_message.data, input_message.len,
                              tag.data);
    }
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  // Should be unreachable.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
}

otcrypto_status_t otcrypto_hmac_init(otcrypto_hmac_context_t *ctx,
                                     const otcrypto_blinded_key_t *key) {
  if (ctx == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the key for null pointers or invalid configurations.
  HARDENED_TRY(check_key(key));

  // Call the appropriate function from the HMAC driver.
  hmac_ctx_t hmac_ctx;
  uint32_t key_block[kHmacMaxBlockWords];
  switch (launder32(key->config.key_mode)) {
    case kOtcryptoKeyModeHmacSha256:
      HARDENED_CHECK_EQ(key->config.key_mode, kOtcryptoKeyModeHmacSha256);
      HARDENED_TRY(key_block_get(key, kHmacSha256BlockWords, key_block));
      hmac_hmac_sha256_init(key_block, &hmac_ctx);
      break;
    case kOtcryptoKeyModeHmacSha384:
      HARDENED_CHECK_EQ(key->config.key_mode, kOtcryptoKeyModeHmacSha384);
      HARDENED_TRY(key_block_get(key, kHmacSha384BlockWords, key_block));
      hmac_hmac_sha384_init(key_block, &hmac_ctx);
      break;
    case kOtcryptoKeyModeHmacSha512:
      HARDENED_CHECK_EQ(key->config.key_mode, kOtcryptoKeyModeHmacSha512);
      HARDENED_TRY(key_block_get(key, kHmacSha512BlockWords, key_block));
      hmac_hmac_sha512_init(key_block, &hmac_ctx);
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  memcpy(ctx->data, &hmac_ctx, sizeof(hmac_ctx));
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_hmac_update(
    otcrypto_hmac_context_t *const ctx,
    otcrypto_const_byte_buf_t input_message) {
  if (ctx == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check for null input message with nonzero length.
  if (input_message.data == NULL && input_message.len != 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  hmac_ctx_t *hmac_ctx = (hmac_ctx_t *)ctx->data;
  return hmac_update(hmac_ctx, input_message.data, input_message.len);
}

otcrypto_status_t otcrypto_hmac_final(otcrypto_hmac_context_t *const ctx,
                                      otcrypto_word32_buf_t tag) {
  if (ctx == NULL || tag.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the digest length.
  hmac_ctx_t *hmac_ctx = (hmac_ctx_t *)ctx->data;
  if (launder32(tag.len) != hmac_ctx->digest_wordlen) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(tag.len, hmac_ctx->digest_wordlen);

  return hmac_final(hmac_ctx, tag.data);
}
