// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/crypto/aes_gcm_testutils.h"

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/aes.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/profile.h"
#include "sw/device/lib/testing/test_framework/check.h"

#define MODULE_ID MAKE_MODULE_ID('a', 'g', 't')

/**
 * Static mask to use for testing.
 */
static const uint32_t kKeyMask[8] = {
    0x01234567, 0x89abcdef, 0x00010203, 0x04050607,
    0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617,
};

enum {
  /**
   * Byte-length of AAD chunks for streaming interface tests.
   */
  kStreamingAadChunkBytes = 10,
  /**
   * Byte-length of message chunks for streaming interface tests.
   */
  kStreamingMessageChunkBytes = 20,
};

/**
 * Get the enum value for a given tag length.
 */
static otcrypto_aes_gcm_tag_len_t get_tag_length(size_t tag_len_bytes) {
  switch (tag_len_bytes) {
    case (128 / 8):
      return kOtcryptoAesGcmTagLen128;
    case (96 / 8):
      return kOtcryptoAesGcmTagLen96;
    case (64 / 8):
      return kOtcryptoAesGcmTagLen64;
    case (32 / 8):
      return kOtcryptoAesGcmTagLen32;
    default:
      // Should not get here.
      CHECK(false);
  }
  // Should not get here.
  CHECK(false);
  return 0;
}

/**
 * Stream an AES-GCM operation (encrypt or decrypt).
 *
 * The caller should call `otcrypto_aes_gcm_*_init()` before this operation and
 * `otcrypto_aes_gcm_*_final()` after.
 *
 * @param ctx AES-GCM context, modified in-place.
 * @param aad Associated data.
 * @param input Plaintext for encryption, or ciphertext for decryption.
 * @param[out] output Ciphertext for encryption, or plaintext for decryption.
 * @param[out] output_bytes_written Number of output bytes written.
 * @return OK or error.
 */
static status_t stream_gcm(otcrypto_aes_gcm_context_t *ctx,
                           otcrypto_const_byte_buf_t aad,
                           otcrypto_const_byte_buf_t input,
                           otcrypto_byte_buf_t output,
                           size_t *output_bytes_written) {
  // Stream the AAD. The last chunk may have a different length than the others.
  if (aad.len > 0) {
    size_t num_chunks = ceil_div(aad.len, kStreamingAadChunkBytes);
    for (size_t i = 0; i < num_chunks; i++) {
      size_t offset = i * kStreamingAadChunkBytes;
      size_t chunk_len = kStreamingAadChunkBytes;
      if (offset + chunk_len > aad.len) {
        chunk_len = aad.len - offset;
      }
      otcrypto_const_byte_buf_t aad_chunk = {
          .data = aad.data + offset,
          .len = chunk_len,
      };
      TRY(otcrypto_aes_gcm_update_aad(ctx, aad_chunk));
    }
  }

  // Stream the input, similary to the AAD except that this time we need to
  // accumulate incremental parts of the output.
  *output_bytes_written = 0;
  if (input.len > 0) {
    size_t num_chunks = ceil_div(input.len, kStreamingMessageChunkBytes);
    for (size_t i = 0; i < num_chunks; i++) {
      size_t offset = i * kStreamingMessageChunkBytes;
      size_t chunk_len = kStreamingMessageChunkBytes;
      if (offset + chunk_len > input.len) {
        chunk_len = input.len - offset;
      }
      otcrypto_const_byte_buf_t input_chunk = {
          .data = input.data + offset,
          .len = chunk_len,
      };
      otcrypto_byte_buf_t output_with_offset = {
          .data = output.data + *output_bytes_written,
          .len = output.len - *output_bytes_written,
      };
      size_t bytes_written_for_chunk = 0;
      TRY(otcrypto_aes_gcm_update_encrypted_data(
          ctx, input_chunk, output_with_offset, &bytes_written_for_chunk));
      *output_bytes_written += bytes_written_for_chunk;
    }
  }
  return OTCRYPTO_OK;
}

status_t aes_gcm_testutils_encrypt(const aes_gcm_test_t *test, bool streaming,
                                   uint32_t *cycles) {
  // Construct the blinded key configuration.
  otcrypto_key_config_t config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeAesGcm,
      .key_length = test->key_len * sizeof(uint32_t),
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };

  // Construct blinded key from the key and testing mask.
  uint32_t keyblob[keyblob_num_words(config)];
  TRY(keyblob_from_key_and_mask(test->key, kKeyMask, config, keyblob));

  // Construct the blinded key.
  otcrypto_blinded_key_t key = {
      .config = config,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
      .checksum = 0,
  };

  // Set the checksum.
  key.checksum = integrity_blinded_checksum(&key);

  size_t iv_num_words =
      (test->iv_len + sizeof(uint32_t) - 1) / sizeof(uint32_t);
  uint32_t iv_data[iv_num_words];
  memcpy(iv_data, test->iv, test->iv_len);
  otcrypto_const_word32_buf_t iv = {
      .data = iv_data,
      .len = iv_num_words,
  };
  otcrypto_const_byte_buf_t plaintext = {
      .data = test->plaintext,
      .len = test->plaintext_len,
  };
  otcrypto_const_byte_buf_t aad = {
      .data = test->aad,
      .len = test->aad_len,
  };

  size_t tag_num_words =
      (test->tag_len + sizeof(uint32_t) - 1) / sizeof(uint32_t);
  uint32_t actual_tag_data[tag_num_words];
  otcrypto_word32_buf_t actual_tag = {
      .data = actual_tag_data,
      .len = tag_num_words,
  };

  size_t ciphertext_blocks = ceil_div(test->plaintext_len, kAesBlockNumBytes);
  uint8_t actual_ciphertext_data[ciphertext_blocks * kAesBlockNumBytes];
  otcrypto_byte_buf_t actual_ciphertext = {
      .data = actual_ciphertext_data,
      .len = test->plaintext_len,
  };

  otcrypto_aes_gcm_tag_len_t tag_len = get_tag_length(test->tag_len);

  if (streaming) {
    uint64_t t_start = profile_start();
    otcrypto_aes_gcm_context_t ctx;
    TRY(otcrypto_aes_gcm_encrypt_init(&key, iv, &ctx));
    size_t ciphertext_bytes_written;
    TRY(stream_gcm(&ctx, aad, plaintext, actual_ciphertext,
                   &ciphertext_bytes_written));
    otcrypto_byte_buf_t final_ciphertext = {
        .data = actual_ciphertext.data + ciphertext_bytes_written,
        .len = test->plaintext_len - ciphertext_bytes_written,
    };
    TRY(otcrypto_aes_gcm_encrypt_final(&ctx, tag_len, final_ciphertext,
                                       &ciphertext_bytes_written, actual_tag));
    *cycles = profile_end(t_start);
  } else {
    // Call encrypt() with a cycle count timing profile.
    uint64_t t_start = profile_start();
    otcrypto_status_t err = otcrypto_aes_gcm_encrypt(
        &key, plaintext, iv, aad, tag_len, actual_ciphertext, actual_tag);
    *cycles = profile_end(t_start);

    // Check for errors.
    TRY(err);
  }

  // Check that the tag and plaintext match expected values.
  if (test->plaintext_len > 0) {
    TRY_CHECK_ARRAYS_EQ(actual_ciphertext_data, test->ciphertext,
                        test->plaintext_len);
  }
  TRY_CHECK_ARRAYS_EQ((unsigned char *)actual_tag_data, test->tag,
                      test->tag_len);

  return OK_STATUS();
}

status_t aes_gcm_testutils_decrypt(const aes_gcm_test_t *test,
                                   hardened_bool_t *tag_valid, bool streaming,
                                   uint32_t *cycles) {
  // Construct the blinded key configuration.
  otcrypto_key_config_t config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeAesGcm,
      .key_length = test->key_len * sizeof(uint32_t),
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };

  // Construct blinded key from the key and testing mask.
  uint32_t keyblob[keyblob_num_words(config)];
  TRY(keyblob_from_key_and_mask(test->key, kKeyMask, config, keyblob));

  // Construct the blinded key.
  otcrypto_blinded_key_t key = {
      .config = config,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
      .checksum = 0,
  };

  // Set the checksum.
  key.checksum = integrity_blinded_checksum(&key);

  size_t iv_num_words =
      (test->iv_len + sizeof(uint32_t) - 1) / sizeof(uint32_t);
  uint32_t iv_data[iv_num_words];
  memcpy(iv_data, test->iv, test->iv_len);
  otcrypto_const_word32_buf_t iv = {
      .data = iv_data,
      .len = iv_num_words,
  };
  otcrypto_const_byte_buf_t ciphertext = {
      .data = test->ciphertext,
      .len = test->plaintext_len,
  };
  otcrypto_const_byte_buf_t aad = {
      .data = test->aad,
      .len = test->aad_len,
  };
  size_t tag_num_words =
      (test->tag_len + sizeof(uint32_t) - 1) / sizeof(uint32_t);
  uint32_t tag_data[tag_num_words];
  memcpy(tag_data, test->tag, test->tag_len);
  otcrypto_const_word32_buf_t tag = {
      .data = tag_data,
      .len = tag_num_words,
  };

  size_t ciphertext_blocks = ceil_div(test->plaintext_len, kAesBlockNumBytes);
  uint8_t actual_plaintext_data[ciphertext_blocks * kAesBlockNumBytes];
  otcrypto_byte_buf_t actual_plaintext = {
      .data = actual_plaintext_data,
      .len = test->plaintext_len,
  };

  otcrypto_aes_gcm_tag_len_t tag_len = get_tag_length(test->tag_len);

  if (streaming) {
    otcrypto_aes_gcm_context_t ctx;
    uint64_t t_start = profile_start();
    TRY(otcrypto_aes_gcm_decrypt_init(&key, iv, &ctx));
    size_t plaintext_bytes_written;
    TRY(stream_gcm(&ctx, aad, ciphertext, actual_plaintext,
                   &plaintext_bytes_written));
    otcrypto_byte_buf_t final_plaintext = {
        .data = actual_plaintext.data + plaintext_bytes_written,
        .len = actual_plaintext.len - plaintext_bytes_written,
    };
    size_t final_plaintext_bytes_written;
    TRY(otcrypto_aes_gcm_decrypt_final(&ctx, tag, tag_len, final_plaintext,
                                       &final_plaintext_bytes_written,
                                       tag_valid));
    *cycles = profile_end(t_start);
  } else {
    // Call decrypt() with a cycle count timing profile.
    icache_invalidate();
    uint64_t t_start = profile_start();
    otcrypto_status_t err = otcrypto_aes_gcm_decrypt(
        &key, ciphertext, iv, aad, tag_len, tag, actual_plaintext, tag_valid);
    *cycles = profile_end(t_start);
    icache_invalidate();

    // Check for errors.
    TRY(err);
  }

  // Check the results.
  if (test->plaintext_len > 0 && *tag_valid == kHardenedBoolTrue) {
    TRY_CHECK_ARRAYS_EQ(actual_plaintext_data, test->plaintext,
                        test->plaintext_len);
  }

  return OK_STATUS();
}
