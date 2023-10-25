// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/mac.h"

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/kmac.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/sha2/sha256.h"
#include "sw/device/lib/crypto/impl/sha2/sha512.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/hash.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('m', 'a', 'c')

OT_WARN_UNUSED_RESULT
crypto_status_t otcrypto_hmac(const crypto_blinded_key_t *key,
                              crypto_const_byte_buf_t input_message,
                              hash_mode_t hash_mode, crypto_word32_buf_t *tag) {
  // Compute HMAC using the streaming API.
  hmac_context_t ctx;
  HARDENED_TRY(otcrypto_hmac_init(&ctx, key, hash_mode));
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
                                   const crypto_blinded_key_t *key,
                                   hash_mode_t hash_mode) {
  if (ctx == NULL || key == NULL || key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (key->config.hw_backed != kHardenedBoolFalse) {
    // TODO(#15590): Add support for sideloaded keys via a custom OTBN program.
    return OTCRYPTO_NOT_IMPLEMENTED;
  }
  if (key->config.security_level != kSecurityLevelLow) {
    // TODO: Harden SHA2 implementations.
    return OTCRYPTO_NOT_IMPLEMENTED;
  }

  // Ensure the key is for HMAC and the hash function matches, and remember the
  // digest and message block sizes.
  size_t digest_words = 0;
  size_t message_block_words = 0;
  switch (key->config.key_mode) {
    case kKeyModeHmacSha256:
      if (hash_mode != kHashModeSha256) {
        return OTCRYPTO_BAD_ARGS;
      }
      digest_words = kSha256DigestWords;
      message_block_words = kSha256MessageBlockWords;
      break;
    case kKeyModeHmacSha384:
      if (hash_mode != kHashModeSha384) {
        return OTCRYPTO_BAD_ARGS;
      }
      digest_words = kSha384DigestWords;
      // Since SHA-512 and SHA-384 have the same core, they use the same
      // message block size.
      message_block_words = kSha512MessageBlockWords;
      break;
    case kKeyModeHmacSha512:
      if (hash_mode != kHashModeSha512) {
        return OTCRYPTO_BAD_ARGS;
      }
      digest_words = kSha512DigestWords;
      message_block_words = kSha512MessageBlockWords;
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_NE(digest_words, 0);
  HARDENED_CHECK_NE(message_block_words, 0);
  HARDENED_CHECK_LE(digest_words, message_block_words);

  // Check the integrity of the key.
  if (integrity_blinded_key_check(key) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Get pointers to key shares.
  uint32_t *share0;
  uint32_t *share1;
  HARDENED_TRY(keyblob_to_shares(key, &share0, &share1));

  // TODO: Once we have hardened SHA2, do not unmask the key here.
  uint32_t unmasked_key[keyblob_share_num_words(key->config)];
  for (size_t i = 0; i < keyblob_share_num_words(key->config); i++) {
    unmasked_key[i] = share0[i] ^ share1[i];
  }

  // Initialize the key block, K0. See FIPS 198-1, section 4.
  uint32_t k0[message_block_words];
  memset(k0, 0, sizeof(k0));
  if (key->config.key_length < (digest_words * sizeof(uint32_t))) {
    // Key is too short.
    return OTCRYPTO_BAD_ARGS;
  } else if (key->config.key_length <= message_block_words * sizeof(uint32_t)) {
    // If the key fits into the message block size, we just need to copy it
    // into the first part of K0.
    hardened_memcpy(k0, unmasked_key, ARRAYSIZE(unmasked_key));
    // If the key size isn't a multiple of the word size, zero the last few
    // bytes.
    size_t offset = key->config.key_length % sizeof(uint32_t);
    if (offset != 0) {
      unsigned char *k0_bytes = (unsigned char *)k0;
      size_t num_zero_bytes = sizeof(uint32_t) - offset;
      unsigned char *dest = k0_bytes + (sizeof(unmasked_key) - num_zero_bytes);
      memset(dest, 0, num_zero_bytes);
    }
  } else {
    // If the key is longer than the hash function block size, we need to hash
    // it and write the digest into the start of K0.
    hash_digest_t key_digest = {
        .len = digest_words,
        .data = k0,
        .mode = hash_mode,
    };
    HARDENED_TRY(otcrypto_hash(
        (crypto_const_byte_buf_t){
            .len = key->config.key_length,
            .data = (unsigned char *)unmasked_key,
        },
        &key_digest));
  }

  // Compute (K0 ^ ipad).
  uint32_t inner_block[message_block_words];
  for (size_t i = 0; i < message_block_words; i++) {
    inner_block[i] = k0[i] ^ 0x36363636;
  }

  // Compute (K0 ^ opad).
  uint32_t outer_block[message_block_words];
  for (size_t i = 0; i < message_block_words; i++) {
    outer_block[i] = k0[i] ^ 0x5c5c5c5c;
  }

  // Start computing inner hash = H(K0 ^ ipad) || message).
  HARDENED_TRY(otcrypto_hash_init(&ctx->inner, hash_mode));
  HARDENED_TRY(otcrypto_hash_update(
      &ctx->inner,
      (crypto_const_byte_buf_t){.len = sizeof(inner_block),
                                .data = (unsigned char *)inner_block}));

  // Start computing outer hash = H(K0 ^ opad || inner).
  HARDENED_TRY(otcrypto_hash_init(&ctx->outer, hash_mode));
  return otcrypto_hash_update(
      &ctx->outer,
      (crypto_const_byte_buf_t){.len = sizeof(outer_block),
                                .data = (unsigned char *)outer_block});
}

crypto_status_t otcrypto_hmac_update(hmac_context_t *const ctx,
                                     crypto_const_byte_buf_t input_message) {
  if (ctx == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Append the message to the inner block.
  return otcrypto_hash_update(&ctx->inner, input_message);
}

crypto_status_t otcrypto_hmac_final(hmac_context_t *const ctx,
                                    crypto_word32_buf_t *tag) {
  if (ctx == NULL || tag == NULL || tag->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Create digest buffer that points to the tag.
  hash_digest_t digest_buf = {
      .mode = ctx->inner.mode,
      .len = tag->len,
      .data = tag->data,
  };

  // Finalize the computation of the inner hash = H(K0 ^ ipad || message) and
  // store it in `tag` temporarily.
  HARDENED_TRY(otcrypto_hash_final(&ctx->inner, &digest_buf));

  // Finalize the computation of the outer hash
  //    = H(K0 ^ opad || H(K0 ^ ipad || message)).
  HARDENED_TRY(otcrypto_hash_update(
      &ctx->outer,
      (crypto_const_byte_buf_t){.len = sizeof(uint32_t) * tag->len,
                                .data = (unsigned char *)tag->data}));

  return otcrypto_hash_final(&ctx->outer, &digest_buf);
}
