// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/crypto/aes_gcm_testutils.h"

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/aes.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/profile.h"
#include "sw/device/lib/testing/test_framework/check.h"

/**
 * Static mask to use for testing.
 */
static const uint32_t kKeyMask[8] = {
    0x01234567, 0x89abcdef, 0x00010203, 0x04050607,
    0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617,
};

/**
 * Get the enum value for a given tag length.
 */
static aead_gcm_tag_len_t get_tag_length(size_t tag_len_bytes) {
  switch (tag_len_bytes) {
    case (128 / 8):
      return kAeadGcmTagLen128;
    case (120 / 8):
      return kAeadGcmTagLen120;
    case (112 / 8):
      return kAeadGcmTagLen112;
    case (104 / 8):
      return kAeadGcmTagLen104;
    case (96 / 8):
      return kAeadGcmTagLen96;
    case (64 / 8):
      return kAeadGcmTagLen64;
    case (32 / 8):
      return kAeadGcmTagLen32;
    default:
      // Should not get here.
      CHECK(false);
  }
  // Should not get here.
  CHECK(false);
  return 0;
}

uint32_t call_aes_gcm_encrypt(aes_gcm_test_t test) {
  // Construct the blinded key configuration.
  crypto_key_config_t config = {
      .version = kCryptoLibVersion1,
      .key_mode = kKeyModeAesGcm,
      .key_length = test.key_len * sizeof(uint32_t),
      .hw_backed = kHardenedBoolFalse,
      .diversification_hw_backed = NULL,
      .security_level = kSecurityLevelLow,
  };

  // Construct blinded key from the key and testing mask.
  uint32_t keyblob[keyblob_num_words(config)];
  CHECK_STATUS_OK(
      keyblob_from_key_and_mask(test.key, kKeyMask, config, keyblob));

  // Construct the blinded key.
  crypto_blinded_key_t key = {
      .config = config,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
      .checksum = 0,
  };

  // Set the checksum.
  key.checksum = integrity_blinded_checksum(&key);

  crypto_const_uint8_buf_t iv = {
      .data = test.iv,
      .len = test.iv_len,
  };
  crypto_const_uint8_buf_t plaintext = {
      .data = test.plaintext,
      .len = test.plaintext_len,
  };
  crypto_const_uint8_buf_t aad = {
      .data = test.aad,
      .len = test.aad_len,
  };

  uint8_t actual_tag_data[test.tag_len];
  crypto_uint8_buf_t actual_tag = {
      .data = actual_tag_data,
      .len = sizeof(actual_tag_data),
  };

  uint8_t actual_ciphertext_data[test.plaintext_len];
  crypto_uint8_buf_t actual_ciphertext = {
      .data = actual_ciphertext_data,
      .len = sizeof(actual_ciphertext_data),
  };

  aead_gcm_tag_len_t tag_len = get_tag_length(test.tag_len);

  // Call encrypt() with a cycle count timing profile.
  uint64_t t_start = profile_start();
  crypto_status_t err = otcrypto_aes_encrypt_gcm(
      &key, plaintext, iv, aad, tag_len, &actual_ciphertext, &actual_tag);
  uint32_t cycles = profile_end_and_print(t_start, "aes_gcm_encrypt");

  // Check for errors and that the tag and plaintext match expected values.
  CHECK(err == kCryptoStatusOK);
  CHECK_ARRAYS_EQ(actual_tag_data, test.tag, test.tag_len);
  if (test.plaintext_len > 0) {
    int cmp =
        memcmp(actual_ciphertext_data, test.ciphertext, test.plaintext_len);
    CHECK(cmp == 0, "AES-GCM encryption output does not match ciphertext");
  }

  return cycles;
}

uint32_t call_aes_gcm_decrypt(aes_gcm_test_t test, bool tag_valid) {
  // Construct the blinded key configuration.
  crypto_key_config_t config = {
      .version = kCryptoLibVersion1,
      .key_mode = kKeyModeAesGcm,
      .key_length = test.key_len * sizeof(uint32_t),
      .hw_backed = kHardenedBoolFalse,
      .diversification_hw_backed = NULL,
      .security_level = kSecurityLevelLow,
  };

  // Construct blinded key from the key and testing mask.
  uint32_t keyblob[keyblob_num_words(config)];
  CHECK_STATUS_OK(
      keyblob_from_key_and_mask(test.key, kKeyMask, config, keyblob));

  // Construct the blinded key.
  crypto_blinded_key_t key = {
      .config = config,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
      .checksum = 0,
  };

  // Set the checksum.
  key.checksum = integrity_blinded_checksum(&key);

  crypto_const_uint8_buf_t iv = {
      .data = test.iv,
      .len = test.iv_len,
  };
  crypto_const_uint8_buf_t ciphertext = {
      .data = test.ciphertext,
      .len = test.plaintext_len,
  };
  crypto_const_uint8_buf_t aad = {
      .data = test.aad,
      .len = test.aad_len,
  };
  crypto_const_uint8_buf_t tag = {
      .data = test.tag,
      .len = test.tag_len,
  };

  uint8_t actual_plaintext_data[test.plaintext_len];
  crypto_uint8_buf_t actual_plaintext = {
      .data = actual_plaintext_data,
      .len = sizeof(actual_plaintext_data),
  };

  aead_gcm_tag_len_t tag_len = get_tag_length(test.tag_len);
  hardened_bool_t success;

  // Call decrypt() with a cycle count timing profile.
  uint64_t t_start = profile_start();
  crypto_status_t err = otcrypto_aes_decrypt_gcm(
      &key, ciphertext, iv, aad, tag_len, tag, &actual_plaintext, &success);
  uint32_t cycles = profile_end_and_print(t_start, "aes_gcm_decrypt");

  // Check the results.
  CHECK(err == kCryptoStatusOK);
  if (tag_valid) {
    CHECK(success == kHardenedBoolTrue,
          "AES-GCM decryption failed on valid input");
    if (test.plaintext_len > 0) {
      int cmp =
          memcmp(actual_plaintext_data, test.plaintext, test.plaintext_len);
      CHECK(cmp == 0, "AES-GCM decryption output does not match plaintext");
    }
  } else {
    CHECK(success == kHardenedBoolFalse,
          "AES-GCM decryption passed an invalid tag");
  }

  return cycles;
}
