// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/mac.h"

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/hmac.h"
#include "sw/device/lib/crypto/drivers/kmac.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/hash.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('m', 'a', 'c')

/**
 * Ensure that the hash context is large enough for HMAC driver struct.
 */
static_assert(
    sizeof(otcrypto_hmac_context_t) >= sizeof(hmac_ctx_t),
    "`otcrypto_hash_context_t` must be big enough to hold `hmac_ctx_t`.");

/**
 * Ensure that HMAC driver struct is suitable for `hardened_memcpy()`.
 */
static_assert(sizeof(hmac_ctx_t) % sizeof(uint32_t) == 0,
              "Size of `hmac_ctx_t` must be a multiple of the word size for "
              "`hardened_memcpy()`");

/**
 * Save the internal HMAC driver context to a generic Hmac context.
 *
 * @param[out] ctx Generic hash context to copy to.
 * @param hmac_ctx The internal context object from HMAC driver.
 */
static void hmac_ctx_save(otcrypto_hmac_context_t *restrict ctx,
                          const hmac_ctx_t *restrict hmac_ctx) {
  // As per the `hardened_memcpy()` documentation, it is OK to cast to
  // `uint32_t *` here as long as `state` is word-aligned, which it must be
  // because all its fields are.
  hardened_memcpy(ctx->data, (uint32_t *)hmac_ctx,
                  sizeof(hmac_ctx_t) / sizeof(uint32_t));
}

/**
 * Restore an internal HMAC driver context from a generic Hmac context.
 *
 * @param ctx Generic hash context to restore from.
 * @param[out] hmac_ctx Destination HMAC driver context object.
 */
static void hmac_ctx_restore(const otcrypto_hmac_context_t *restrict ctx,
                             hmac_ctx_t *restrict hmac_ctx) {
  // As per the `hardened_memcpy()` documentation, it is OK to cast to
  // `uint32_t *` here as long as `state` is word-aligned, which it must be
  // because all its fields are.
  hardened_memcpy((uint32_t *)hmac_ctx, ctx->data,
                  sizeof(hmac_ctx_t) / sizeof(uint32_t));
}

/**
 * For given `key_mode`, return the corresponding driver-level `hmac_mode` and
 * `block_size`. `block_size` is the internal block size of the hash function
 * implied by `hash_mode`, and its unit is words.
 *
 * This function must only be used with HMAC key modes, otherwise an error
 * is returned.
 *
 * @param key_mode The input key mode.
 * @param[out] hmac_mode HMAC driver-level equivalent of `key_mode`.
 * @param[out] block_size The internal block size of the hash function
 * associated with `hmac_mode`.
 * @return Result of the operation.
 */
static status_t get_hmac_mode(otcrypto_key_mode_t key_mode,
                              hmac_mode_t *hmac_mode, size_t *block_size) {
  switch (key_mode) {
    case kOtcryptoKeyModeHmacSha256:
      *hmac_mode = kHmacModeHmac256;
      *block_size = kHmacSha256BlockWords;
      break;
    case kOtcryptoKeyModeHmacSha384:
      *hmac_mode = kHmacModeHmac384;
      // Note that HMAC-384 and HMAC-512 have the same internal block size.
      *block_size = kHmacSha512BlockWords;
      break;
    case kOtcryptoKeyModeHmacSha512:
      *hmac_mode = kHmacModeHmac512;
      *block_size = kHmacSha512BlockWords;
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }
  return OTCRYPTO_OK;
}

/**
 * Pad or hash HMAC key to full block. I.e. compute K0 as defined in FIPS 198-1,
 * Section 4, Steps 1-3.
 *
 * For HMAC-256, `processed_key` is 512 bits, and for HMAC-384/512,
 * `processed_key` is 1024 bits.
 *
 * The caller must allocate `processed_key` buffer with internal block size.
 *
 * @param key The blinded input key.
 * @param[out] processed_key Padding/hashed key whose size matches the internal
 * block size of the hash function.
 * @return Result of the operation.
 */
static status_t hmac_key_process(const otcrypto_blinded_key_t *key,
                                 uint32_t *processed_key) {
  otcrypto_hash_mode_t hash_mode;
  size_t block_size;
  size_t digest_size;
  switch (key->config.key_mode) {
    case kOtcryptoKeyModeHmacSha256:
      hash_mode = kOtcryptoHashModeSha256;
      block_size = kHmacSha256BlockWords;
      digest_size = kHmacSha256DigestWords;
      break;
    case kOtcryptoKeyModeHmacSha384:
      hash_mode = kOtcryptoHashModeSha384;
      // Note that HMAC-384 and HMAC-512 have the same internal block size.
      block_size = kHmacSha512BlockWords;
      digest_size = kHmacSha384DigestWords;
      break;
    case kOtcryptoKeyModeHmacSha512:
      hash_mode = kOtcryptoHashModeSha512;
      block_size = kHmacSha512BlockWords;
      digest_size = kHmacSha512DigestWords;
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  // HMAC HWIP does not support masking, so we need to unmask the key.
  size_t unmasked_key_len = keyblob_share_num_words(key->config);
  uint32_t unmasked_key[unmasked_key_len];
  HARDENED_TRY(keyblob_key_unmask(key, unmasked_key_len, unmasked_key));

  // Pre-populate with 0s, in order to pad keys smaller than the internal
  // block size, according to FIPS 198-1, Section 4.
  memset(processed_key, 0, block_size * sizeof(uint32_t));
  // If the key is larger than the internal block size, we need to hash it
  // according to FIPS 198-1, Section 4, Step 2.
  if (key->config.key_length > block_size * sizeof(uint32_t)) {
    otcrypto_hash_digest_t key_digest = {
        .mode = hash_mode,
        .data = processed_key,
        .len = digest_size,
    };
    otcrypto_const_byte_buf_t msg_buf = {
        .len = key->config.key_length,
        .data = (unsigned char *)unmasked_key,
    };
    HARDENED_TRY(otcrypto_hash(msg_buf, key_digest));
  } else {
    hardened_memcpy(processed_key, unmasked_key, unmasked_key_len);
    // If the key size isn't a multiple of the word size, zero the last few
    // bytes.
    size_t offset = key->config.key_length % sizeof(uint32_t);
    if (offset != 0) {
      unsigned char *key_end_ptr =
          (unsigned char *)&processed_key[unmasked_key_len];
      size_t num_zero_bytes = sizeof(uint32_t) - offset;
      memset(key_end_ptr - num_zero_bytes, 0, num_zero_bytes);
    }
  }
  return OTCRYPTO_OK;
}

OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_hmac(const otcrypto_blinded_key_t *key,
                                otcrypto_const_byte_buf_t input_message,
                                otcrypto_word32_buf_t tag) {
  // Validate key struct.
  if (key == NULL || key->keyblob == NULL || tag.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // HMAC HWIP is not masked and it does not have sideload support, so the
  // following conditions return not implemented.
  if (key->config.hw_backed != kHardenedBoolFalse) {
    return OTCRYPTO_NOT_IMPLEMENTED;
  }
  if (key->config.security_level != kOtcryptoKeySecurityLevelLow) {
    return OTCRYPTO_NOT_IMPLEMENTED;
  }

  // Check for null input message with nonzero length.
  if (input_message.data == NULL && input_message.len != 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  hmac_mode_t hmac_mode;
  size_t block_size;
  HARDENED_TRY(get_hmac_mode(key->config.key_mode, &hmac_mode, &block_size));

  uint32_t processed_key[block_size];
  HARDENED_TRY(hmac_key_process(key, processed_key));

  return hmac(hmac_mode, processed_key, block_size, input_message.data,
              input_message.len, tag.data, tag.len);
}

OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_kmac(const otcrypto_blinded_key_t *key,
                                otcrypto_const_byte_buf_t input_message,
                                otcrypto_kmac_mode_t kmac_mode,
                                otcrypto_const_byte_buf_t customization_string,
                                size_t required_output_len,
                                otcrypto_word32_buf_t tag) {
  // TODO (#16410) Revisit/complete error checks

  // Check for null pointers.
  if (key == NULL || key->keyblob == NULL || tag.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check for null input message with nonzero length.
  if (input_message.data == NULL && input_message.len != 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check for null customization string with nonzero length.
  if (customization_string.data == NULL && customization_string.len != 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Ensure that tag buffer length and `required_output_len` match each other.
  if (required_output_len != tag.len * sizeof(uint32_t) ||
      required_output_len == 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  size_t key_len = keyblob_share_num_words(key->config) * sizeof(uint32_t);

  // Check `key_len` is valid/supported by KMAC HWIP.
  HARDENED_TRY(kmac_key_length_check(key_len));

  // Check the integrity of the blinded key.
  if (integrity_blinded_key_check(key) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }

  kmac_blinded_key_t kmac_key = {
      .share0 = NULL,
      .share1 = NULL,
      .hw_backed = key->config.hw_backed,
      .len = key_len,
  };

  if (key->config.hw_backed == kHardenedBoolTrue) {
    if (key_len != kKmacSideloadKeyLength / 8) {
      return OTCRYPTO_BAD_ARGS;
    }
    // Configure keymgr with diversification input and then generate the
    // sideload key.
    keymgr_diversification_t diversification;
    // Diversification call also checks that `key->keyblob_length` is 8 words
    // long.
    HARDENED_TRY(keyblob_to_keymgr_diversification(key, &diversification));
    HARDENED_TRY(keymgr_generate_key_kmac(diversification));
  } else if (key->config.hw_backed == kHardenedBoolFalse) {
    // Check `key_len` matches `keyblob_length`.
    if (key->keyblob_length != 2 * key->config.key_length) {
      return OTCRYPTO_BAD_ARGS;
    }
    HARDENED_TRY(keyblob_to_shares(key, &kmac_key.share0, &kmac_key.share1));
  } else {
    return OTCRYPTO_BAD_ARGS;
  }

  switch (kmac_mode) {
    case kOtcryptoKmacModeKmac128:
      // Check `key_mode` matches `mac_mode`
      if (key->config.key_mode != kOtcryptoKeyModeKmac128) {
        return OTCRYPTO_BAD_ARGS;
      }
      HARDENED_TRY(kmac_kmac_128(&kmac_key, input_message.data,
                                 input_message.len, customization_string.data,
                                 customization_string.len, tag.data, tag.len));
      break;
    case kOtcryptoKmacModeKmac256:
      // Check `key_mode` matches `mac_mode`
      if (key->config.key_mode != kOtcryptoKeyModeKmac256) {
        return OTCRYPTO_BAD_ARGS;
      }

      HARDENED_TRY(kmac_kmac_256(&kmac_key, input_message.data,
                                 input_message.len, customization_string.data,
                                 customization_string.len, tag.data, tag.len));
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  if (key->config.hw_backed == kHardenedBoolTrue) {
    HARDENED_TRY(keymgr_sideload_clear_kmac());
  } else if (key->config.hw_backed != kHardenedBoolFalse) {
    return OTCRYPTO_BAD_ARGS;
  }

  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_hmac_init(otcrypto_hmac_context_t *ctx,
                                     const otcrypto_blinded_key_t *key) {
  if (ctx == NULL || key == NULL || key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (key->config.hw_backed != kHardenedBoolFalse) {
    // TODO(#15590): Add support for sideloaded keys via a custom OTBN program.
    return OTCRYPTO_NOT_IMPLEMENTED;
  }
  if (key->config.security_level != kOtcryptoKeySecurityLevelLow) {
    // TODO: Harden SHA2 implementations.
    return OTCRYPTO_NOT_IMPLEMENTED;
  }

  // Ensure the key is for HMAC and the hash function matches, and remember the
  // digest and message block sizes.
  hmac_mode_t hmac_mode;
  size_t block_size;
  HARDENED_TRY(get_hmac_mode(key->config.key_mode, &hmac_mode, &block_size));

  uint32_t processed_key[block_size];
  HARDENED_TRY(hmac_key_process(key, processed_key));

  hmac_ctx_t hmac_ctx;
  HARDENED_TRY(hmac_init(&hmac_ctx, hmac_mode, processed_key, block_size));
  hmac_ctx_save(ctx, &hmac_ctx);
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

  hmac_ctx_t hmac_ctx;
  hmac_ctx_restore(ctx, &hmac_ctx);
  HARDENED_TRY(hmac_update(&hmac_ctx, input_message.data, input_message.len));
  hmac_ctx_save(ctx, &hmac_ctx);
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_hmac_final(otcrypto_hmac_context_t *const ctx,
                                      otcrypto_word32_buf_t tag) {
  if (ctx == NULL || tag.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  hmac_ctx_t hmac_ctx;
  hmac_ctx_restore(ctx, &hmac_ctx);
  HARDENED_TRY(hmac_final(&hmac_ctx, tag.data, tag.len));
  // TODO(#23191): Clear `ctx`.
  hmac_ctx_save(ctx, &hmac_ctx);
  return OTCRYPTO_OK;
}
