// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/aes_gcm.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/aes.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/drivers/keymgr.h"
#include "sw/device/lib/crypto/drivers/rv_core_ibex.h"
#include "sw/device/lib/crypto/impl/aes_gcm/aes_gcm.h"
#include "sw/device/lib/crypto/impl/aes_gcm/ghash.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('a', 'g', 'c')

// Check GHASH context size against the underlying implementation.
static_assert(sizeof(otcrypto_aes_gcm_context_t) >= sizeof(aes_gcm_context_t),
              "Size of AES-GCM context object for top-level API must be at "
              "least as large as the context for the "
              "underlying implementation.");
static_assert(alignof(aes_gcm_context_t) >= alignof(uint32_t),
              "Internal AES-GCM context object must be word-aligned for use "
              "with `hardened_memcpy`.");
static_assert(sizeof(otcrypto_key_config_t) % sizeof(uint32_t) == 0,
              "Key configuration size should be a multiple of 32 bits");

// Ensure the internal AES-GCM context size is a multiple of the word size and
// calculate the number of words.
static_assert(sizeof(aes_gcm_context_t) % sizeof(uint32_t) == 0,
              "Internal AES-GCM context object must be a multiple of the word "
              "size for use with `hardened_memcpy`.");
enum {
  kAesGcmContextNumWords = sizeof(aes_gcm_context_t) / sizeof(uint32_t),
};

/**
 * Save an AES-GCM context.
 *
 * @param internal_ctx Internal context object to save.
 * @param[out] api_ctx Resulting API-facing context object.
 */
static inline void gcm_context_save(aes_gcm_context_t *internal_ctx,
                                    otcrypto_aes_gcm_context_t *api_ctx) {
  hardened_memcpy(api_ctx->data, (uint32_t *)internal_ctx,
                  kAesGcmContextNumWords);
}

/**
 * Restore an AES-GCM context.
 *
 * @param api_ctx API-facing context object to restore from.
 * @param[out] internal_ctx Resulting internal context object.
 */
static inline void gcm_context_restore(otcrypto_aes_gcm_context_t *api_ctx,
                                       aes_gcm_context_t *internal_ctx) {
  hardened_memcpy((uint32_t *)internal_ctx, api_ctx->data,
                  kAesGcmContextNumWords);
}

/**
 * Construct the underlying AES key for AES-GCM.
 *
 * Also performs integrity, mode, and null-pointer checks on the key.
 *
 * Re-masks the key after checking its integrity. The caller should ensure the
 * entropy complex is up before calling this function.
 *
 * @param blinded_key Blinded key struct.
 * @param[out] aes_key Destination AES key struct.
 * @return Result of the operation.
 */
static status_t aes_gcm_key_construct(otcrypto_blinded_key_t *blinded_key,
                                      aes_key_t *aes_key) {
  // Key integrity check.
  if (launder32(integrity_blinded_key_check(blinded_key)) !=
      kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(integrity_blinded_key_check(blinded_key),
                    kHardenedBoolTrue);

  // Check the key mode.
  if (launder32((uint32_t)blinded_key->config.key_mode) !=
      kOtcryptoKeyModeAesGcm) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(blinded_key->config.key_mode, kOtcryptoKeyModeAesGcm);

  // Set the mode of the underlying AES key to CTR (since this is the
  // underlying block cipher mode for GCM).
  aes_key->mode = kAesCipherModeCtr;

  // Set the AES key length (in words).
  aes_key->key_len = keyblob_share_num_words(blinded_key->config);

  // Check for null pointer.
  if (blinded_key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (launder32(blinded_key->config.hw_backed) == kHardenedBoolTrue) {
    // In this case, we use an implementation-specific representation; the
    // first "share" is the keyblob and the second share is ignored.
    if (launder32(blinded_key->keyblob_length) != kKeyblobHwBackedBytes) {
      return OTCRYPTO_BAD_ARGS;
    }
    HARDENED_CHECK_EQ(blinded_key->keyblob_length, kKeyblobHwBackedBytes);
    aes_key->key_shares[0] = blinded_key->keyblob;
    aes_key->key_shares[1] = NULL;
    aes_key->sideload = launder32(kHardenedBoolTrue);
  } else if (launder32(blinded_key->config.hw_backed) == kHardenedBoolFalse) {
    HARDENED_CHECK_EQ(blinded_key->config.hw_backed, kHardenedBoolFalse);

    // Remask the key.
    HARDENED_TRY(keyblob_remask(blinded_key));

    // Get pointers to the individual shares.
    uint32_t *share0;
    uint32_t *share1;
    HARDENED_TRY(keyblob_to_shares(blinded_key, &share0, &share1));
    aes_key->key_shares[0] = share0;
    aes_key->key_shares[1] = share1;
    aes_key->sideload = launder32(kHardenedBoolFalse);
  } else {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(aes_key->sideload, blinded_key->config.hw_backed);

  return OTCRYPTO_OK;
}

/**
 * Checks if the given byte-length matches the tag length enum value.
 *
 * @param word_len Allocated tag length in 32-bit words.
 * @param tag_len Tag length enum value.
 * @return OK if the tag length is acceptable, BAD_ARGS otherwise.
 */
status_t aes_gcm_check_tag_length(size_t word_len,
                                  otcrypto_aes_gcm_tag_len_t tag_len) {
  size_t bit_len = 0;
  switch (launder32(tag_len)) {
    case kOtcryptoAesGcmTagLen128:
      HARDENED_CHECK_EQ(tag_len, kOtcryptoAesGcmTagLen128);
      bit_len = 128;
      break;
    case kOtcryptoAesGcmTagLen96:
      HARDENED_CHECK_EQ(tag_len, kOtcryptoAesGcmTagLen96);
      bit_len = 96;
      break;
    case kOtcryptoAesGcmTagLen64:
      HARDENED_CHECK_EQ(tag_len, kOtcryptoAesGcmTagLen64);
      bit_len = 64;
      break;
    case kOtcryptoAesGcmTagLen32:
      HARDENED_CHECK_EQ(tag_len, kOtcryptoAesGcmTagLen32);
      bit_len = 32;
      break;
    default:
      // Invalid tag length.
      return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_GT(bit_len, 0);
  HARDENED_CHECK_EQ(bit_len % 32, 0);

  if (launder32(word_len) != bit_len / 32) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(word_len, bit_len / 32);

  // Extra hardening checks; the word length must be nonzero and at most the
  // size of an AES block.
  HARDENED_CHECK_LT(0, word_len);
  HARDENED_CHECK_LE(word_len, kAesBlockNumWords);

  return OTCRYPTO_OK;
}

/**
 * Actuate the key manager to generate a sideloaded AES-GCM key.
 *
 * The AES driver will not load or clear sideloaded keys by itself, so we need
 * to do it separately at each stage of the AES-GCM operation.
 *
 * Sideloaded keys are stored in the `aes_key_t` struct in a format specific to
 * this AES-GCM implementation: the first "key share" is the diversification
 * data as it would be stored in a blinded keyblob, and the second "share" is
 * completely ignored.
 *
 * If the key is not a sideloaded key, this function does nothing.
 *
 * @param key Key to load.
 * @return OK or errror.
 */
static status_t load_key_if_sideloaded(const aes_key_t key) {
  if (launder32(key.sideload) == kHardenedBoolFalse) {
    return OTCRYPTO_OK;
  } else if (key.sideload != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(key.sideload, kHardenedBoolTrue);
  keymgr_diversification_t diversification;
  HARDENED_TRY(keyblob_buffer_to_keymgr_diversification(
      key.key_shares[0], kOtcryptoKeyModeAesGcm, &diversification));
  return keymgr_generate_key_aes(diversification);
}

/**
 * Clear the sideload slot if the AES key was sideloaded.
 *
 * It is important to clear the sideload slot before returning to the caller so
 * that other applications can't access the key in between operations.
 *
 * If the key is not a sideloaded key, this function does nothing.
 *
 * @param key Key that was possibly loaded.
 * @return OK or errror.
 */
static status_t clear_key_if_sideloaded(const aes_key_t key) {
  if (launder32(key.sideload) == kHardenedBoolFalse) {
    HARDENED_CHECK_EQ(key.sideload, kHardenedBoolFalse);
    return OTCRYPTO_OK;
  } else if (launder32(key.sideload) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(key.sideload, kHardenedBoolTrue);
  return keymgr_sideload_clear_aes();
}

otcrypto_status_t otcrypto_aes_gcm_encrypt(otcrypto_blinded_key_t *key,
                                           otcrypto_const_byte_buf_t plaintext,
                                           otcrypto_const_word32_buf_t iv,
                                           otcrypto_const_byte_buf_t aad,
                                           otcrypto_aes_gcm_tag_len_t tag_len,
                                           otcrypto_byte_buf_t ciphertext,
                                           otcrypto_word32_buf_t auth_tag) {
  // Check for NULL pointers in input pointers and required-nonzero-length data
  // buffers.
  if (key == NULL || iv.data == NULL || auth_tag.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Ensure entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  // Conditionally check for null pointers in data buffers that may be
  // 0-length.
  if ((aad.len != 0 && aad.data == NULL) ||
      (ciphertext.len != 0 && ciphertext.data == NULL) ||
      (plaintext.len != 0 && plaintext.data == NULL)) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Ensure the plaintext and ciphertext lengths match.
  if (launder32(ciphertext.len) != plaintext.len) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(ciphertext.len, plaintext.len);

  // Check the tag length.
  HARDENED_TRY(aes_gcm_check_tag_length(auth_tag.len, tag_len));

  // Construct the AES key.
  aes_key_t aes_key;
  HARDENED_TRY(aes_gcm_key_construct(key, &aes_key));
  HARDENED_TRY(load_key_if_sideloaded(aes_key));

  // Call the core encryption operation.
  HARDENED_TRY(aes_gcm_encrypt(aes_key, iv.len, iv.data, plaintext.len,
                               plaintext.data, aad.len, aad.data, auth_tag.len,
                               auth_tag.data, ciphertext.data));

  HARDENED_TRY(clear_key_if_sideloaded(aes_key));
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_aes_gcm_decrypt(
    otcrypto_blinded_key_t *key, otcrypto_const_byte_buf_t ciphertext,
    otcrypto_const_word32_buf_t iv, otcrypto_const_byte_buf_t aad,
    otcrypto_aes_gcm_tag_len_t tag_len, otcrypto_const_word32_buf_t auth_tag,
    otcrypto_byte_buf_t plaintext, hardened_bool_t *success) {
  // Check for NULL pointers in input pointers and required-nonzero-length data
  // buffers.
  if (key == NULL || iv.data == NULL || auth_tag.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Conditionally check for null pointers in data buffers that may be
  // 0-length.
  if ((aad.len != 0 && aad.data == NULL) ||
      (ciphertext.len != 0 && ciphertext.data == NULL) ||
      (plaintext.len != 0 && plaintext.data == NULL)) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Ensure entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  // Construct the AES key.
  aes_key_t aes_key;
  HARDENED_TRY(aes_gcm_key_construct(key, &aes_key));
  HARDENED_TRY(load_key_if_sideloaded(aes_key));

  // Ensure the plaintext and ciphertext lengths match.
  if (launder32(ciphertext.len) != plaintext.len) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(ciphertext.len, plaintext.len);

  // Check the tag length.
  HARDENED_TRY(aes_gcm_check_tag_length(auth_tag.len, tag_len));

  // Call the core decryption operation.
  HARDENED_TRY(aes_gcm_decrypt(aes_key, iv.len, iv.data, ciphertext.len,
                               ciphertext.data, aad.len, aad.data, auth_tag.len,
                               auth_tag.data, plaintext.data, success));

  HARDENED_TRY(clear_key_if_sideloaded(aes_key));
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_aes_gcm_encrypt_init(
    otcrypto_blinded_key_t *key, otcrypto_const_word32_buf_t iv,
    otcrypto_aes_gcm_context_t *ctx) {
  if (key == NULL || key->keyblob == NULL || iv.data == NULL || ctx == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Ensure entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  // Construct the AES key.
  aes_key_t aes_key;
  HARDENED_TRY(aes_gcm_key_construct(key, &aes_key));
  HARDENED_TRY(load_key_if_sideloaded(aes_key));

  // Call the internal init operation.
  aes_gcm_context_t internal_ctx;
  HARDENED_TRY(aes_gcm_encrypt_init(aes_key, iv.len, iv.data, &internal_ctx));

  // Save the context and clear the key if needed.
  gcm_context_save(&internal_ctx, ctx);
  HARDENED_TRY(clear_key_if_sideloaded(internal_ctx.key));
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_aes_gcm_decrypt_init(
    otcrypto_blinded_key_t *key, otcrypto_const_word32_buf_t iv,
    otcrypto_aes_gcm_context_t *ctx) {
  if (key == NULL || key->keyblob == NULL || iv.data == NULL || ctx == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Ensure entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  // Construct the AES key.
  aes_key_t aes_key;
  HARDENED_TRY(aes_gcm_key_construct(key, &aes_key));
  HARDENED_TRY(load_key_if_sideloaded(aes_key));

  // Call the internal init operation.
  aes_gcm_context_t internal_ctx;
  HARDENED_TRY(aes_gcm_decrypt_init(aes_key, iv.len, iv.data, &internal_ctx));

  // Save the context and clear the key if needed.
  gcm_context_save(&internal_ctx, ctx);
  HARDENED_TRY(clear_key_if_sideloaded(internal_ctx.key));
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_aes_gcm_update_aad(otcrypto_aes_gcm_context_t *ctx,
                                              otcrypto_const_byte_buf_t aad) {
  if (ctx == NULL || aad.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Ensure entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  if (aad.len == 0) {
    // Nothing to do.
    return OTCRYPTO_OK;
  }

  // Restore the AES-GCM context object and load the key if needed.
  aes_gcm_context_t internal_ctx;
  gcm_context_restore(ctx, &internal_ctx);
  HARDENED_TRY(load_key_if_sideloaded(internal_ctx.key));

  // Call the internal update operation.
  HARDENED_TRY(aes_gcm_update_aad(&internal_ctx, aad.len, aad.data));

  // Save the context and clear the key if needed.
  gcm_context_save(&internal_ctx, ctx);
  HARDENED_TRY(clear_key_if_sideloaded(internal_ctx.key));
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_aes_gcm_update_encrypted_data(
    otcrypto_aes_gcm_context_t *ctx, otcrypto_const_byte_buf_t input,
    otcrypto_byte_buf_t output, size_t *output_bytes_written) {
  if (ctx == NULL || input.data == NULL || output.data == NULL ||
      output_bytes_written == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  *output_bytes_written = 0;

  // Ensure entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  if (input.len == 0) {
    // Nothing to do.
    return OTCRYPTO_OK;
  }

  // Restore the AES-GCM context object and load the key if needed.
  aes_gcm_context_t internal_ctx;
  gcm_context_restore(ctx, &internal_ctx);
  HARDENED_TRY(load_key_if_sideloaded(internal_ctx.key));

  // The output buffer must be long enough to hold all full blocks that will
  // exist after `input` is added.
  size_t partial_block_len = internal_ctx.input_len % kAesBlockNumBytes;
  if (input.len > UINT32_MAX - partial_block_len) {
    return OTCRYPTO_BAD_ARGS;
  }
  size_t min_output_blocks =
      (partial_block_len + input.len) / kAesBlockNumBytes;
  size_t min_output_len = min_output_blocks * kAesBlockNumBytes;
  if (output.len < min_output_len) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Call the internal update operation.
  HARDENED_TRY(aes_gcm_update_encrypted_data(
      &internal_ctx, input.len, input.data, output_bytes_written, output.data));

  // Save the context and clear the key if needed.
  gcm_context_save(&internal_ctx, ctx);
  HARDENED_TRY(clear_key_if_sideloaded(internal_ctx.key));
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_aes_gcm_encrypt_final(
    otcrypto_aes_gcm_context_t *ctx, otcrypto_aes_gcm_tag_len_t tag_len,
    otcrypto_byte_buf_t ciphertext, size_t *ciphertext_bytes_written,
    otcrypto_word32_buf_t auth_tag) {
  if (ctx == NULL || ciphertext_bytes_written == NULL ||
      auth_tag.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (ciphertext.len != 0 && ciphertext.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  *ciphertext_bytes_written = 0;

  // Ensure entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  // Check the tag length.
  HARDENED_TRY(aes_gcm_check_tag_length(auth_tag.len, tag_len));

  // Restore the AES-GCM context object and load the key if needed.
  aes_gcm_context_t internal_ctx;
  gcm_context_restore(ctx, &internal_ctx);
  HARDENED_TRY(load_key_if_sideloaded(internal_ctx.key));

  // If the partial block is nonempty, the output must be at least as long as
  // the partial block.
  size_t partial_block_len = internal_ctx.input_len % kAesBlockNumBytes;
  if (ciphertext.len < partial_block_len) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Call the internal final operation.
  HARDENED_TRY(aes_gcm_encrypt_final(&internal_ctx, auth_tag.len, auth_tag.data,
                                     ciphertext_bytes_written,
                                     ciphertext.data));

  // Clear the context and the key if needed.
  hardened_memshred(ctx->data, ARRAYSIZE(ctx->data));
  HARDENED_TRY(clear_key_if_sideloaded(internal_ctx.key));
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_aes_gcm_decrypt_final(
    otcrypto_aes_gcm_context_t *ctx, otcrypto_const_word32_buf_t auth_tag,
    otcrypto_aes_gcm_tag_len_t tag_len, otcrypto_byte_buf_t plaintext,
    size_t *plaintext_bytes_written, hardened_bool_t *success) {
  if (ctx == NULL || plaintext_bytes_written == NULL || auth_tag.data == NULL ||
      success == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (plaintext.len != 0 && plaintext.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  *plaintext_bytes_written = 0;
  *success = kHardenedBoolFalse;

  // Entropy complex needs to be initialized for `memshred`.
  HARDENED_TRY(entropy_complex_check());

  // Check the tag length.
  HARDENED_TRY(aes_gcm_check_tag_length(auth_tag.len, tag_len));

  // Restore the AES-GCM context object and load the key if needed.
  aes_gcm_context_t internal_ctx;
  gcm_context_restore(ctx, &internal_ctx);
  HARDENED_TRY(load_key_if_sideloaded(internal_ctx.key));

  // If the partial block is nonempty, the output must be at least as long as
  // the partial block.
  size_t partial_block_len = internal_ctx.input_len % kAesBlockNumBytes;
  if (plaintext.len < partial_block_len) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Call the internal final operation.
  HARDENED_TRY(aes_gcm_decrypt_final(&internal_ctx, auth_tag.len, auth_tag.data,
                                     plaintext_bytes_written, plaintext.data,
                                     success));

  // Clear the context and the key if needed.
  hardened_memshred(ctx->data, ARRAYSIZE(ctx->data));
  HARDENED_TRY(clear_key_if_sideloaded(internal_ctx.key));
  return OTCRYPTO_OK;
}
