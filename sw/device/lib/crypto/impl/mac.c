// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/mac.h"

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/kmac.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/sha2/sha256.h"
#include "sw/device/lib/crypto/impl/status.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('m', 'a', 'c')

/**
 * Ensure that the hmac context is large enough.
 *
 * The HMAC context should hold one SHA-256 message block and a SHA-256 state
 * object.
 */
static_assert(
    sizeof(hmac_context_t) == kSha256MessageBlockBytes + sizeof(sha256_state_t),
    "hmac_context_t must be the same size as a key block and a SHA-256 state");
/**
 * Ensure that the SHA-256 state struct is suitable for `hardened_memcpy()`.
 */
static_assert(sizeof(sha256_state_t) % sizeof(uint32_t) == 0,
              "Size of sha256_state_t must be a multiple of the word size for "
              "`hardened_memcpy()`");

enum {
  /**
   * Word-offset of the key block within the HMAC context object.
   */
  kHmacContextKeyBlockWordOffset = 0,
  /**
   * Word-offset of the SHA-256 state within the HMAC context object.
   */
  kHmacContextSha256StateWordOffset = kSha256MessageBlockWords,
};

/**
 * Save a SHA-256 state to an HMAC context.
 *
 * @param[out] ctx HMAC context to copy to.
 * @param state SHA-256 state object.
 * @param k0 Key block.
 */
static void sha256_state_save(hmac_context_t *restrict ctx,
                              const sha256_state_t *restrict state) {
  // As per the `hardened_memcpy()` documentation, it
  // is OK to cast to `uint32_t *` here as long as `state` is word-aligned,
  // which it must be because all its fields are.
  uint32_t *dest = ctx->data + kHmacContextSha256StateWordOffset;
  hardened_memcpy(dest, (uint32_t *)state,
                  sizeof(sha256_state_t) / sizeof(uint32_t));
}

/**
 * Restore a SHA-256 state from an HMAC context.
 *
 * @param ctx HMAC context to restore from.
 * @param[out] state Destination SHA-256 state object.
 */
static void sha256_state_restore(const hmac_context_t *restrict ctx,
                                 sha256_state_t *restrict state) {
  // As per the `hardened_memcpy()` documentation, it is OK to cast to
  // `uint32_t *` here as long as `state` is word-aligned, which it must be
  // because all its fields are.
  const uint32_t *src = ctx->data + kHmacContextSha256StateWordOffset;
  hardened_memcpy((uint32_t *)state, src,
                  sizeof(sha256_state_t) / sizeof(uint32_t));
}
/**
 * Save the key block to an HMAC context.
 *
 * @param[out] ctx HMAC context to copy to.
 * @param k0 Key block to save.
 */
static void key_block_save(hmac_context_t *restrict ctx,
                           const uint32_t *restrict k0) {
  uint32_t *dest = ctx->data + kHmacContextKeyBlockWordOffset;
  hardened_memcpy(dest, k0, kSha256MessageBlockWords);
}

/**
 * Restore a key block from an HMAC context.
 *
 * @param ctx HMAC context to restore from.
 * @param[out] k0 Destination key block buffer.
 */
static void key_block_restore(const hmac_context_t *restrict ctx,
                              uint32_t *restrict k0) {
  const uint32_t *src = ctx->data + kHmacContextKeyBlockWordOffset;
  hardened_memcpy(k0, src, kSha256MessageBlockWords);
}

crypto_status_t otcrypto_mac_keygen(crypto_blinded_key_t *key) {
  // TODO: Implement KMAC sideloaded key generation once we have a keymgr
  // driver. In the meantime, non-sideloaded KMAC or HMAC keys can simply be
  // generated using the DRBG and key-import functions.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

OT_WARN_UNUSED_RESULT
crypto_status_t otcrypto_hmac(const crypto_blinded_key_t *key,
                              crypto_const_byte_buf_t input_message,
                              crypto_word32_buf_t *tag) {
  // Compute HMAC using the streaming API.
  hmac_context_t ctx;
  HARDENED_TRY(otcrypto_hmac_init(&ctx, key));
  HARDENED_TRY(otcrypto_hmac_update(&ctx, input_message));
  return otcrypto_hmac_final(&ctx, tag);
}

OT_WARN_UNUSED_RESULT
crypto_status_t otcrypto_kmac(const crypto_blinded_key_t *key,
                              crypto_const_byte_buf_t input_message,
                              kmac_mode_t kmac_mode,
                              crypto_const_byte_buf_t customization_string,
                              size_t required_output_len,
                              crypto_word32_buf_t *tag) {
  // TODO (#16410) Revisit/complete error checks

  // Check for null pointers.
  if (key == NULL || key->keyblob == NULL || tag == NULL || tag->data == NULL) {
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

  // Ensure that the output will fit in the tag buffer.
  if (required_output_len > tag->len * sizeof(uint32_t) ||
      tag->len > SIZE_MAX / sizeof(uint32_t)) {
    return OTCRYPTO_BAD_ARGS;
  }

  size_t key_len = keyblob_share_num_words(key->config) * sizeof(uint32_t);

  // Check `key_len` is valid/supported by KMAC HWIP.
  HARDENED_TRY(kmac_key_length_check(key_len));

  // Check the integrity of the blinded key.
  if (integrity_blinded_key_check(key) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }

  // TODO (#16410, #15590): Add sideload support.
  if (key->config.hw_backed == kHardenedBoolTrue) {
    return OTCRYPTO_NOT_IMPLEMENTED;
  }

  kmac_blinded_key_t kmac_key;
  HARDENED_TRY(keyblob_to_shares(key, &kmac_key.share0, &kmac_key.share1));
  kmac_key.len = key_len;

  switch (kmac_mode) {
    case kMacModeKmac128:
      // Check `key_mode` matches `mac_mode`
      if (key->config.key_mode != kKeyModeKmac128) {
        return OTCRYPTO_BAD_ARGS;
      }
      HARDENED_TRY(kmac_kmac_128(&kmac_key, input_message.data,
                                 input_message.len, customization_string.data,
                                 customization_string.len, tag->data,
                                 tag->len));
      break;
    case kMacModeKmac256:
      // Check `key_mode` matches `mac_mode`
      if (key->config.key_mode != kKeyModeKmac256) {
        return OTCRYPTO_BAD_ARGS;
      }

      HARDENED_TRY(kmac_kmac_256(&kmac_key, input_message.data,
                                 input_message.len, customization_string.data,
                                 customization_string.len, tag->data,
                                 tag->len));
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  return OTCRYPTO_OK;
}

crypto_status_t otcrypto_hmac_init(hmac_context_t *ctx,
                                   const crypto_blinded_key_t *key) {
  if (ctx == NULL || key == NULL || key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (key->config.hw_backed != kHardenedBoolFalse) {
    // TODO(#15590): Add support for sideloaded keys.
    return OTCRYPTO_NOT_IMPLEMENTED;
  }

  // Key mode must be HMAC-SHA256.
  if (key->config.key_mode != kKeyModeHmacSha256) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the integrity of the key.
  if (integrity_blinded_key_check(key) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Get pointers to key shares.
  uint32_t *share0;
  uint32_t *share1;
  HARDENED_TRY(keyblob_to_shares(key, &share0, &share1));

  // TODO: Once we have hardened SHA-256, do not unmask the key here.
  uint32_t unmasked_key[keyblob_share_num_words(key->config)];
  for (size_t i = 0; i < keyblob_share_num_words(key->config); i++) {
    unmasked_key[i] = share0[i] ^ share1[i];
  }

  // Initialize the key block, K0. See FIPS 198-1, section 4.
  uint32_t k0[kSha256MessageBlockWords] = {0};
  if (key->config.key_length <= kSha256MessageBlockBytes) {
    // If the key fits into the SHA-256 block size, we just need to copy it
    // into the first part of K0.
    hardened_memcpy(k0, unmasked_key, ARRAYSIZE(unmasked_key));
  } else {
    // If the key is longer than the SHA-256 block size, we need to hash it
    // and write the digest into the start of K0.
    HARDENED_TRY(
        sha256((unsigned char *)unmasked_key, key->config.key_length, k0));
  }

  // Compute SHA256(K0 ^ ipad).
  uint32_t inner_block[kSha256MessageBlockWords];
  for (size_t i = 0; i < kSha256MessageBlockWords; i++) {
    inner_block[i] = k0[i] ^ 0x36363636;
  }

  // Start computing SHA256(K0 ^ ipad) || message).
  sha256_state_t sha256_ctx;
  sha256_init(&sha256_ctx);
  HARDENED_TRY(sha256_update(&sha256_ctx, (unsigned char *)inner_block,
                             sizeof(inner_block)));

  // Save the key block and SHA-256 state.
  key_block_save(ctx, k0);
  sha256_state_save(ctx, &sha256_ctx);

  return OTCRYPTO_OK;
}

crypto_status_t otcrypto_hmac_update(hmac_context_t *const ctx,
                                     crypto_const_byte_buf_t input_message) {
  if (ctx == NULL || (input_message.data == NULL && input_message.len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }

  sha256_state_t sha256_ctx;
  sha256_state_restore(ctx, &sha256_ctx);
  HARDENED_TRY(
      sha256_update(&sha256_ctx, input_message.data, input_message.len));
  sha256_state_save(ctx, &sha256_ctx);
  return OTCRYPTO_OK;
}

crypto_status_t otcrypto_hmac_final(hmac_context_t *const ctx,
                                    crypto_word32_buf_t *tag) {
  if (ctx == NULL || tag == NULL || tag->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (tag->len != kSha256DigestWords) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Restore the SHA-256 state from the context.
  sha256_state_t sha256_ctx;
  sha256_state_restore(ctx, &sha256_ctx);

  // Finalize the computation of SHA256(K0 ^ ipad || message).
  uint32_t inner_digest[kSha256DigestWords];
  HARDENED_TRY(sha256_final(&sha256_ctx, inner_digest));

  // Restore the key block K0 from the context.
  uint32_t k0[kSha256MessageBlockWords];
  key_block_restore(ctx, k0);

  // Compute K0 ^ opad.
  uint32_t outer_block[kSha256MessageBlockWords];
  for (size_t i = 0; i < kSha256MessageBlockWords; i++) {
    outer_block[i] = k0[i] ^ 0x5c5c5c5c;
  }

  // Start a new hash computation to get the final tag: SHA256(K0 ^ opad ||
  // SHA256(K0 ^ ipad || message))
  sha256_init(&sha256_ctx);
  HARDENED_TRY(sha256_update(&sha256_ctx, (unsigned char *)outer_block,
                             sizeof(outer_block)));
  HARDENED_TRY(sha256_update(&sha256_ctx, (unsigned char *)inner_digest,
                             sizeof(inner_digest)));
  HARDENED_TRY(sha256_final(&sha256_ctx, tag->data));

  return OTCRYPTO_OK;
}
