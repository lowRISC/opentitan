// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/hmac.h"

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/drivers/hmac.h"
#include "sw/device/lib/crypto/drivers/rv_core_ibex.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/security_config.h"
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
 * Compute the key block (see FIPS 198-1, Section 4, Steps 1-3) together with
 * its checksum.
 *
 * Adds padding and in some cases pre-hashes the HMAC key to get a value the
 * length of the underlying message block size. This length is then set in
 * the key_len field of hmac_key_t.
 *
 * The caller must ensure that at least `key_block_wordlen` 32-bit words of
 * space is allocated at the destination `key_block` buffer.
 *
 * @param key The blinded input key.
 * @param key_block_wordlen Block size in 32-bit words.
 * @param[out] hmac_key Destination of the HMAC key struct.
 * @return Result of the operation.
 */
static status_t hmac_key_construct(const otcrypto_blinded_key_t *key,
                                   size_t key_block_wordlen,
                                   hmac_key_t *hmac_key) {
  // HMAC HWIP does not support masking, so we need to unmask the key.
  size_t unmasked_key_len = keyblob_share_num_words(key->config);
  uint32_t unmasked_key[unmasked_key_len];
  HARDENED_TRY(keyblob_key_unmask(key, unmasked_key_len, unmasked_key));

  // Pre-populate with 0s, in order to pad keys smaller than the internal
  // block size, according to FIPS 198-1, Section 4.
  memset(hmac_key->key_block, 0, key_block_wordlen * sizeof(uint32_t));
  // If the key is larger than the internal block size, we need to hash it
  // according to FIPS 198-1, Section 4, Step 2.
  if (launder32(key->config.key_length) >
      key_block_wordlen * sizeof(uint32_t)) {
    otcrypto_hmac_key_mode_t used_key_mode = launder32(0);
    switch (key->config.key_mode) {
      case kOtcryptoKeyModeHmacSha256:
        if (key->config.security_level == kOtcryptoKeySecurityLevelHigh) {
          // Create an inverted copy of the input key and run the real sha and
          // inverted one in a random order.
          uint32_t key_copy[key_block_wordlen];
          uint32_t random_unmasked_key[unmasked_key_len];
          HARDENED_TRY(
              hardened_memshred(random_unmasked_key, unmasked_key_len));

          bool swap = ibex_rnd32_read() & 0x1;
          if (swap) {
            HARDENED_TRY(hmac_hash_sha256((unsigned char *)random_unmasked_key,
                                          key->config.key_length, key_copy));
            HARDENED_TRY(hmac_hash_sha256((unsigned char *)unmasked_key,
                                          key->config.key_length,
                                          hmac_key->key_block));
          } else {
            HARDENED_TRY(hmac_hash_sha256((unsigned char *)unmasked_key,
                                          key->config.key_length,
                                          hmac_key->key_block));
            HARDENED_TRY(hmac_hash_sha256((unsigned char *)random_unmasked_key,
                                          key->config.key_length, key_copy));
          }
        } else {
          HARDENED_TRY(hmac_hash_sha256((unsigned char *)unmasked_key,
                                        key->config.key_length,
                                        hmac_key->key_block));
        }
        used_key_mode = launder32(used_key_mode) | kOtcryptoKeyModeHmacSha256;
        break;
      case kOtcryptoKeyModeHmacSha384:
        if (key->config.security_level == kOtcryptoKeySecurityLevelHigh) {
          // Create an inverted copy of the input key and run the real sha and
          // inverted one in a random order.
          uint32_t key_copy[key_block_wordlen];
          uint32_t random_unmasked_key[unmasked_key_len];
          HARDENED_TRY(
              hardened_memshred(random_unmasked_key, unmasked_key_len));

          bool swap = ibex_rnd32_read() & 0x1;
          if (swap) {
            HARDENED_TRY(hmac_hash_sha384((unsigned char *)random_unmasked_key,
                                          key->config.key_length, key_copy));
            HARDENED_TRY(hmac_hash_sha384((unsigned char *)unmasked_key,
                                          key->config.key_length,
                                          hmac_key->key_block));
          } else {
            HARDENED_TRY(hmac_hash_sha384((unsigned char *)unmasked_key,
                                          key->config.key_length,
                                          hmac_key->key_block));
            HARDENED_TRY(hmac_hash_sha384((unsigned char *)random_unmasked_key,
                                          key->config.key_length, key_copy));
          }
        } else {
          HARDENED_TRY(hmac_hash_sha384((unsigned char *)unmasked_key,
                                        key->config.key_length,
                                        hmac_key->key_block));
        }
        used_key_mode = launder32(used_key_mode) | kOtcryptoKeyModeHmacSha384;
        break;
      case kOtcryptoKeyModeHmacSha512:
        if (key->config.security_level == kOtcryptoKeySecurityLevelHigh) {
          // Create an inverted copy of the input key and run the real sha and
          // inverted one in a random order.
          uint32_t key_copy[key_block_wordlen];
          uint32_t random_unmasked_key[unmasked_key_len];
          HARDENED_TRY(
              hardened_memshred(random_unmasked_key, unmasked_key_len));

          bool swap = ibex_rnd32_read() & 0x1;
          if (swap) {
            HARDENED_TRY(hmac_hash_sha512((unsigned char *)random_unmasked_key,
                                          key->config.key_length, key_copy));
            HARDENED_TRY(hmac_hash_sha512((unsigned char *)unmasked_key,
                                          key->config.key_length,
                                          hmac_key->key_block));
          } else {
            HARDENED_TRY(hmac_hash_sha512((unsigned char *)unmasked_key,
                                          key->config.key_length,
                                          hmac_key->key_block));
            HARDENED_TRY(hmac_hash_sha512((unsigned char *)random_unmasked_key,
                                          key->config.key_length, key_copy));
          }
        } else {
          HARDENED_TRY(hmac_hash_sha512((unsigned char *)unmasked_key,
                                        key->config.key_length,
                                        hmac_key->key_block));
        }
        used_key_mode = launder32(used_key_mode) | kOtcryptoKeyModeHmacSha512;
        break;
      default:
        return OTCRYPTO_BAD_ARGS;
    }
    HARDENED_CHECK_EQ(used_key_mode, key->config.key_mode);
  } else {
    HARDENED_CHECK_LE(key->config.key_length,
                      key_block_wordlen * sizeof(uint32_t));
    HARDENED_TRY(
        hardened_memcpy(hmac_key->key_block, unmasked_key, unmasked_key_len));
    // If the key size isn't a multiple of the word size, zero the last few
    // bytes.
    size_t offset = key->config.key_length % sizeof(uint32_t);
    if (offset != 0) {
      unsigned char *key_end_ptr =
          (unsigned char *)(&hmac_key->key_block[unmasked_key_len]);
      size_t num_zero_bytes = sizeof(uint32_t) - offset;
      memset(key_end_ptr - num_zero_bytes, 0, num_zero_bytes);
    }
  }

  // Set the key length to the key block word length.
  hmac_key->key_len = key_block_wordlen;

  // Create the checksum of the key and store it in the key structure.
  if (launder32(hmac_key->key_len) > 0) {
    hmac_key->checksum = hmac_key_integrity_checksum(hmac_key);
  } else {
    HARDENED_CHECK_EQ(hmac_key->key_len, 0);
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

  // The underlying HMAC hardware does not have sideload support.
  if (key->config.hw_backed != kHardenedBoolFalse) {
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
  // Preload the tag with randomness.
  HARDENED_TRY(hardened_memshred(tag.data, tag.len));

  // Check the security config of the device.
  HARDENED_TRY(security_config_check(key->config.security_level));

  // Check the key for null pointers or invalid configurations.
  HARDENED_TRY(check_key(key));

  if (key->config.security_level != kOtcryptoKeySecurityLevelLow) {
    // Entropy complex must be initialized for `hardened_memeq`.
    HARDENED_TRY(entropy_complex_check());
  }

  // Call the appropriate function from the HMAC driver.
  hmac_key_t hmac_key;
  switch (key->config.key_mode) {
    case kOtcryptoKeyModeHmacSha256: {
      HARDENED_CHECK_EQ(launder32(key->config.key_mode),
                        kOtcryptoKeyModeHmacSha256);
      HARDENED_TRY(hmac_key_construct(key, kHmacSha256BlockWords, &hmac_key));
      if (key->config.security_level == kOtcryptoKeySecurityLevelLow) {
        // No protection against FI.
        HARDENED_CHECK_EQ(launder32(key->config.security_level),
                          kOtcryptoKeySecurityLevelLow);
        return hmac_hmac_sha256(&hmac_key, input_message.data,
                                input_message.len, tag.data);
      } else if (key->config.security_level ==
                 kOtcryptoKeySecurityLevelMedium) {
        // Call the HMAC core twice and compare both tags. This serves as a FI
        // countermeasure.
        // First HMAC computation using the HMAC core.
        HARDENED_CHECK_EQ(launder32(key->config.security_level),
                          kOtcryptoKeySecurityLevelMedium);
        HARDENED_TRY(hmac_hmac_sha256(&hmac_key, input_message.data,
                                      input_message.len, tag.data));
        // Second HMAC computation using the HMAC core.
        uint32_t tag_redundant[tag.len];
        hmac_key_t hmac_key_redundant;
        HARDENED_TRY(hmac_key_construct(key, kHmacSha256BlockWords,
                                        &hmac_key_redundant));
        HARDENED_TRY(hmac_hmac_sha256(&hmac_key_redundant, input_message.data,
                                      input_message.len, tag_redundant));
        // Comparison of both tags.
        HARDENED_CHECK_EQ(
            hardened_memeq(&tag.data[0], &tag_redundant[0], tag.len),
            kHardenedBoolTrue);
        return OTCRYPTO_OK;
      } else {
        // Perform two HMAC operations. The first call uses the HMAC core. The
        // second use uses a HMAC implementation that does not use the HMAC
        // core. This serves as a FI countermeasure.
        HARDENED_CHECK_EQ(launder32(key->config.security_level),
                          kOtcryptoKeySecurityLevelHigh);
        // First HMAC computation using the HMAC core.
        HARDENED_TRY(hmac_hmac_sha256(&hmac_key, input_message.data,
                                      input_message.len, tag.data));
        // Second HMAC computation without using the HMAC core.
        uint32_t tag_redundant[tag.len];
        hmac_key_t hmac_key_redundant;
        HARDENED_TRY(hmac_key_construct(key, kHmacSha256BlockWords,
                                        &hmac_key_redundant));
        HARDENED_TRY(
            hmac_hmac_sha256_redundant(&hmac_key_redundant, input_message.data,
                                       input_message.len, tag_redundant));
        // Comparison of both tags.
        HARDENED_CHECK_EQ(
            hardened_memeq(&tag.data[0], &tag_redundant[0], tag.len),
            kHardenedBoolTrue);
        return OTCRYPTO_OK;
      }
    }
    case kOtcryptoKeyModeHmacSha384: {
      HARDENED_CHECK_EQ(key->config.key_mode, kOtcryptoKeyModeHmacSha384);
      HARDENED_TRY(hmac_key_construct(key, kHmacSha384BlockWords, &hmac_key));
      if (key->config.security_level == kOtcryptoKeySecurityLevelLow) {
        HARDENED_CHECK_EQ(launder32(key->config.security_level),
                          kOtcryptoKeySecurityLevelLow);
        return hmac_hmac_sha384(&hmac_key, input_message.data,
                                input_message.len, tag.data);
      } else if (key->config.security_level ==
                 kOtcryptoKeySecurityLevelMedium) {
        // Call the HMAC core twice and compare both tags. This serves as a FI
        // countermeasure.
        // First HMAC computation using the HMAC core.
        HARDENED_CHECK_EQ(launder32(key->config.security_level),
                          kOtcryptoKeySecurityLevelMedium);
        HARDENED_TRY(hmac_hmac_sha384(&hmac_key, input_message.data,
                                      input_message.len, tag.data));
        // Second HMAC computation using the HMAC core.
        uint32_t tag_redundant[tag.len];
        hmac_key_t hmac_key_redundant;
        HARDENED_TRY(hmac_key_construct(key, kHmacSha384BlockWords,
                                        &hmac_key_redundant));
        HARDENED_TRY(hmac_hmac_sha384(&hmac_key_redundant, input_message.data,
                                      input_message.len, tag_redundant));
        // Comparison of both tags.
        HARDENED_CHECK_EQ(
            hardened_memeq(&tag.data[0], &tag_redundant[0], tag.len),
            kHardenedBoolTrue);
        return OTCRYPTO_OK;
      } else {
        // Perform two HMAC operations. The first call uses the HMAC core. The
        // second use uses a HMAC implementation that does not use the HMAC
        // core. This serves as a FI countermeasure.
        HARDENED_CHECK_EQ(launder32(key->config.security_level),
                          kOtcryptoKeySecurityLevelHigh);
        // First HMAC computation using the HMAC core.
        HARDENED_TRY(hmac_hmac_sha384(&hmac_key, input_message.data,
                                      input_message.len, tag.data));
        // Second HMAC computation without using the HMAC core.
        uint32_t tag_redundant[tag.len];
        hmac_key_t hmac_key_redundant;
        HARDENED_TRY(hmac_key_construct(key, kHmacSha384BlockWords,
                                        &hmac_key_redundant));
        HARDENED_TRY(
            hmac_hmac_sha384_redundant(&hmac_key_redundant, input_message.data,
                                       input_message.len, tag_redundant));
        // Comparison of both tags.
        HARDENED_CHECK_EQ(
            hardened_memeq(&tag.data[0], &tag_redundant[0], tag.len),
            kHardenedBoolTrue);
        return OTCRYPTO_OK;
      }
    }
    case kOtcryptoKeyModeHmacSha512: {
      HARDENED_CHECK_EQ(key->config.key_mode, kOtcryptoKeyModeHmacSha512);
      HARDENED_TRY(hmac_key_construct(key, kHmacSha512BlockWords, &hmac_key));
      if (key->config.security_level == kOtcryptoKeySecurityLevelLow) {
        HARDENED_CHECK_EQ(launder32(key->config.security_level),
                          kOtcryptoKeySecurityLevelLow);
        return hmac_hmac_sha512(&hmac_key, input_message.data,
                                input_message.len, tag.data);
      } else if (key->config.security_level ==
                 kOtcryptoKeySecurityLevelMedium) {
        // Call the HMAC core twice and compare both tags. This serves as a FI
        // countermeasure.
        // First HMAC computation using the HMAC core.
        HARDENED_CHECK_EQ(launder32(key->config.security_level),
                          kOtcryptoKeySecurityLevelMedium);
        HARDENED_TRY(hmac_hmac_sha512(&hmac_key, input_message.data,
                                      input_message.len, tag.data));
        // Second HMAC computation using the HMAC core.
        uint32_t tag_redundant[tag.len];
        hmac_key_t hmac_key_redundant;
        HARDENED_TRY(hmac_key_construct(key, kHmacSha512BlockWords,
                                        &hmac_key_redundant));
        HARDENED_TRY(hmac_hmac_sha512(&hmac_key_redundant, input_message.data,
                                      input_message.len, tag_redundant));
        // Comparison of both tags.
        HARDENED_CHECK_EQ(
            hardened_memeq(&tag.data[0], &tag_redundant[0], tag.len),
            kHardenedBoolTrue);
        return OTCRYPTO_OK;
      } else {
        // Perform two HMAC operations. The first call uses the HMAC core. The
        // second use uses a HMAC implementation that does not use the HMAC
        // core. This serves as a FI countermeasure.
        HARDENED_CHECK_EQ(launder32(key->config.security_level),
                          kOtcryptoKeySecurityLevelHigh);
        // First HMAC computation using the HMAC core.
        HARDENED_TRY(hmac_hmac_sha512(&hmac_key, input_message.data,
                                      input_message.len, tag.data));
        // Second HMAC computation without using the HMAC core.
        uint32_t tag_redundant[tag.len];
        hmac_key_t hmac_key_redundant;
        HARDENED_TRY(hmac_key_construct(key, kHmacSha512BlockWords,
                                        &hmac_key_redundant));
        HARDENED_TRY(
            hmac_hmac_sha512_redundant(&hmac_key_redundant, input_message.data,
                                       input_message.len, tag_redundant));
        // Comparison of both tags.
        HARDENED_CHECK_EQ(
            hardened_memeq(&tag.data[0], &tag_redundant[0], tag.len),
            kHardenedBoolTrue);
        return OTCRYPTO_OK;
      }
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

  // Only security level low is supported for the streaming mode.
  if (key->config.security_level != kOtcryptoKeySecurityLevelLow) {
    return OTCRYPTO_NOT_IMPLEMENTED;
  }

  // Call the appropriate function from the HMAC driver.
  hmac_ctx_t hmac_ctx;
  hmac_key_t hmac_key;
  otcrypto_hmac_key_mode_t key_mode_used = launder32(0);
  switch (launder32(key->config.key_mode)) {
    case kOtcryptoKeyModeHmacSha256:
      key_mode_used = launder32(key_mode_used) | kOtcryptoKeyModeHmacSha256;
      HARDENED_CHECK_EQ(key->config.key_mode, kOtcryptoKeyModeHmacSha256);
      HARDENED_TRY(hmac_key_construct(key, kHmacSha256BlockWords, &hmac_key));
      hmac_hmac_sha256_init(hmac_key, &hmac_ctx);
      break;
    case kOtcryptoKeyModeHmacSha384:
      key_mode_used = launder32(key_mode_used) | kOtcryptoKeyModeHmacSha384;
      HARDENED_CHECK_EQ(key->config.key_mode, kOtcryptoKeyModeHmacSha384);
      HARDENED_TRY(hmac_key_construct(key, kHmacSha384BlockWords, &hmac_key));
      hmac_hmac_sha384_init(hmac_key, &hmac_ctx);
      break;
    case kOtcryptoKeyModeHmacSha512:
      key_mode_used = launder32(key_mode_used) | kOtcryptoKeyModeHmacSha512;
      HARDENED_CHECK_EQ(key->config.key_mode, kOtcryptoKeyModeHmacSha512);
      HARDENED_TRY(hmac_key_construct(key, kHmacSha512BlockWords, &hmac_key));
      hmac_hmac_sha512_init(hmac_key, &hmac_ctx);
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }
  // Check if we landed in the correct case statement. Use ORs for this to
  // avoid that multiple cases were executed.
  HARDENED_CHECK_EQ(launder32(key_mode_used), key->config.key_mode);

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
