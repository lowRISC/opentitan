// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/cryptolib_build_info.h"
#include "sw/device/lib/crypto/include/entropy_src.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/key_transport.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

// Key configuration for wrapping key (AES-256).
#define kWrappingKeyConfig                            \
  ((otcrypto_key_config_t){                           \
      .version = otcrypto_lib_version(),              \
      .key_mode = kOtcryptoKeyModeAesKwp,             \
      .key_length = 256 / 8,                          \
      .hw_backed = kHardenedBoolFalse,                \
      .security_level = kOtcryptoKeySecurityLevelLow, \
  })

/**
 * Check that wrapping and unwrapping returns the original key.
 *
 * @param key_to_wrap Blinded key to wrap/unwrap.
 * @param kek_kek AES-KWP key to wrap with.
 */
static status_t run_wrap_unwrap(const otcrypto_blinded_key_t *key_to_wrap,
                                const otcrypto_blinded_key_t *key_kek) {
  size_t wrapped_num_words;
  TRY(otcrypto_wrapped_key_len(key_to_wrap->config, &wrapped_num_words));

  // Wrap the key.
  uint32_t wrapped_key_data[wrapped_num_words];
  otcrypto_word32_buf_t wrapped_key = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, wrapped_key_data, ARRAYSIZE(wrapped_key_data));
  TRY(otcrypto_key_wrap(key_to_wrap, key_kek, &wrapped_key));

  // Unwrap the key.
  hardened_bool_t success;
  TRY_CHECK(key_to_wrap->keyblob_length % sizeof(uint32_t) == 0);
  size_t keyblob_words = key_to_wrap->keyblob_length / sizeof(uint32_t);
  uint32_t unwrapped_key_keyblob[keyblob_words];
  otcrypto_blinded_key_t unwrapped_key = {
      .keyblob_length = keyblob_words * sizeof(uint32_t),
      .keyblob = unwrapped_key_keyblob,
  };
  otcrypto_const_word32_buf_t wrapped_key_data_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, wrapped_key_data,
                        ARRAYSIZE(wrapped_key_data));
  TRY(otcrypto_key_unwrap(&wrapped_key_data_buf, key_kek, &success,
                          &unwrapped_key));

  // Check the result.
  TRY_CHECK(success == kHardenedBoolTrue);
  TRY_CHECK_ARRAYS_EQ(unwrapped_key.keyblob, key_to_wrap->keyblob,
                      keyblob_words);
  TRY_CHECK(memcmp(&unwrapped_key.config, &key_to_wrap->config,
                   sizeof(otcrypto_key_config_t)) == 0);
  TRY_CHECK(unwrapped_key.keyblob_length == key_to_wrap->keyblob_length);
  TRY_CHECK(unwrapped_key.checksum == key_to_wrap->checksum);

  // Unwrapping into a key struct with a larger keyblob_length should succeed
  // and update keyblob_length to the exact keyblob size.
  uint32_t larger_keyblob[keyblob_words + 2];
  otcrypto_blinded_key_t larger_len_key = {
      .keyblob_length = sizeof(larger_keyblob),
      .keyblob = larger_keyblob,
  };
  TRY(otcrypto_key_unwrap(&wrapped_key_data_buf, key_kek, &success,
                          &larger_len_key));
  TRY_CHECK(success == kHardenedBoolTrue);
  TRY_CHECK(larger_len_key.keyblob_length == keyblob_words * sizeof(uint32_t));
  TRY_CHECK_ARRAYS_EQ(larger_len_key.keyblob, key_to_wrap->keyblob,
                      keyblob_words);

  // Unwrapping into a key struct with a too-small keyblob_length should fail.
  otcrypto_blinded_key_t bad_len_key = {
      .keyblob_length = (keyblob_words - 1) * sizeof(uint32_t),
      .keyblob = unwrapped_key_keyblob,
  };
  TRY_CHECK(!status_ok(otcrypto_key_unwrap(&wrapped_key_data_buf, key_kek,
                                           &success, &bad_len_key)));

  // Unwrapping a corrupted ciphertext should return OK with success = false.
  wrapped_key_data[0] ^= 1;
  TRY(otcrypto_key_unwrap(&wrapped_key_data_buf, key_kek, &success,
                          &unwrapped_key));
  TRY_CHECK(success == kHardenedBoolFalse);

  return OK_STATUS();
}

/**
 * Test wrapping/unwrapping a random key.
 */
static status_t wrap_unwrap_random_test(void) {
  const otcrypto_key_config_t kKmacKeyConfig = {
      .version = otcrypto_lib_version(),
      .key_mode = kOtcryptoKeyModeKmac128,
      .key_length = 128 / 8,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };

  // Generate a random KMAC key.
  uint32_t keyblob[(kKmacKeyConfig.key_length * 2) / sizeof(uint32_t)];
  otcrypto_blinded_key_t kmac_key = {
      .config = kKmacKeyConfig,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  otcrypto_const_byte_buf_t personalization =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 0);
  TRY(otcrypto_symmetric_keygen(&personalization, &kmac_key));

  // Generate a random AES-KWP key.
  uint32_t kek_keyblob[(kWrappingKeyConfig.key_length * 2) / sizeof(uint32_t)];
  otcrypto_blinded_key_t kek = {
      .config = kWrappingKeyConfig,
      .keyblob_length = sizeof(kek_keyblob),
      .keyblob = kek_keyblob,
  };
  TRY(otcrypto_symmetric_keygen(&personalization, &kek));

  return run_wrap_unwrap(&kmac_key, &kek);
}

/**
 * Test wrapping/unwrapping an RSA-4096 private keyblob (largest supported key).
 */
static status_t wrap_unwrap_rsa4096_test(void) {
  const otcrypto_key_config_t kRsa4096KeyConfig = {
      .version = otcrypto_lib_version(),
      .key_mode = kOtcryptoKeyModeRsaSignPkcs,
      .key_length = 4096 / 8,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };

  // RSA-4096 private keyblob stores d0, d1, n (128 words each) and checksum (1
  // word).
  uint32_t rsa_keyblob[3 * (4096 / 32) + 1];
  for (size_t i = 0; i < ARRAYSIZE(rsa_keyblob); i++) {
    rsa_keyblob[i] = 0xa5a50000u ^ (uint32_t)i;
  }
  otcrypto_blinded_key_t rsa_key = {
      .config = kRsa4096KeyConfig,
      .keyblob_length = sizeof(rsa_keyblob),
      .keyblob = rsa_keyblob,
  };
  rsa_key.checksum = otcrypto_integrity_blinded_checksum(&rsa_key);

  // Import a 256-bit AES-KWP key encryption key.
  const uint32_t kKekShare0[8] = {
      0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f,
      0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f,
  };
  const uint32_t kKekShare1[8] = {
      0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff,
      0xe0e1e2e3, 0xe4e5e6e7, 0xe8e9eaeb, 0xecedeeef,
  };
  otcrypto_const_word32_buf_t kek_share0 = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, kKekShare0, ARRAYSIZE(kKekShare0));
  otcrypto_const_word32_buf_t kek_share1 = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, kKekShare1, ARRAYSIZE(kKekShare1));
  uint32_t kek_keyblob[(kWrappingKeyConfig.key_length * 2) / sizeof(uint32_t)];
  otcrypto_blinded_key_t kek = {
      .config = kWrappingKeyConfig,
      .keyblob_length = sizeof(kek_keyblob),
      .keyblob = kek_keyblob,
  };
  TRY(otcrypto_import_blinded_key(&kek_share0, &kek_share1, &kek));

  return run_wrap_unwrap(&rsa_key, &kek);
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t result = OK_STATUS();

  otcrypto_state_t state = {0};
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow, &state));
  EXECUTE_TEST(result, wrap_unwrap_random_test);
  EXECUTE_TEST(result, wrap_unwrap_rsa4096_test);

  return status_ok(result);
}
