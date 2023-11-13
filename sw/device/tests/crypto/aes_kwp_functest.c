// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/include/aes.h"
#include "sw/device/lib/crypto/include/key_transport.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

// Key configuration for wrapping key (AES-256).
static const crypto_key_config_t kWrappingKeyConfig = {
    .version = kCryptoLibVersion1,
    .key_mode = kKeyModeAesKwp,
    .key_length = 256 / 8,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kSecurityLevelLow,
};

/**
 * Check that wrapping and unwrapping returns the original key.
 *
 * @param key_to_wrap Blinded key to wrap/unwrap.
 * @param kek_kek AES-KWP key to wrap with.
 */
static status_t run_wrap_unwrap(const crypto_blinded_key_t *key_to_wrap,
                                const crypto_blinded_key_t *key_kek) {
  size_t wrapped_num_words;
  TRY(otcrypto_aes_kwp_wrapped_len(key_to_wrap->config, &wrapped_num_words));

  // Wrap the key.
  uint32_t wrapped_key_data[wrapped_num_words];
  crypto_word32_buf_t wrapped_key = {
      .data = wrapped_key_data,
      .len = ARRAYSIZE(wrapped_key_data),
  };
  TRY(otcrypto_aes_kwp_wrap(key_to_wrap, key_kek, &wrapped_key));

  // Unwrap the key.
  hardened_bool_t success;
  TRY_CHECK(key_to_wrap->keyblob_length % sizeof(uint32_t) == 0);
  size_t keyblob_words = key_to_wrap->keyblob_length / sizeof(uint32_t);
  uint32_t unwrapped_key_keyblob[keyblob_words];
  crypto_blinded_key_t unwrapped_key = {
      .keyblob_length = keyblob_words * sizeof(uint32_t),
      .keyblob = unwrapped_key_keyblob,
  };
  TRY(otcrypto_aes_kwp_unwrap(
      (crypto_const_word32_buf_t){
          .data = wrapped_key_data,
          .len = ARRAYSIZE(wrapped_key_data),
      },
      key_kek, &success, &unwrapped_key));

  // Check the result.
  TRY_CHECK(success == kHardenedBoolTrue);
  TRY_CHECK_ARRAYS_EQ(unwrapped_key.keyblob, key_to_wrap->keyblob,
                      keyblob_words);
  TRY_CHECK(memcmp(&unwrapped_key.config, &key_to_wrap->config,
                   sizeof(crypto_key_config_t)) == 0);
  TRY_CHECK(unwrapped_key.keyblob_length == key_to_wrap->keyblob_length);
  TRY_CHECK(unwrapped_key.checksum == key_to_wrap->checksum);

  return OK_STATUS();
}

/**
 * Test wrapping/unwrapping a random key.
 */
static status_t wrap_unwrap_random_test(void) {
  const crypto_key_config_t kKmacKeyConfig = {
      .version = kCryptoLibVersion1,
      .key_mode = kKeyModeKmac128,
      .key_length = 128 / 8,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kSecurityLevelLow,
  };

  // Generate a random KMAC key.
  uint32_t keyblob[(kKmacKeyConfig.key_length * 2) / sizeof(uint32_t)];
  crypto_blinded_key_t kmac_key = {
      .config = kKmacKeyConfig,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  crypto_const_byte_buf_t personalization = {.data = NULL, .len = 0};
  TRY(otcrypto_symmetric_keygen(personalization, &kmac_key));

  // Generate a random AES-KWP key.
  uint32_t kek_keyblob[(kWrappingKeyConfig.key_length * 2) / sizeof(uint32_t)];
  crypto_blinded_key_t kek = {
      .config = kWrappingKeyConfig,
      .keyblob_length = sizeof(kek_keyblob),
      .keyblob = kek_keyblob,
  };
  TRY(otcrypto_symmetric_keygen(personalization, &kek));

  return run_wrap_unwrap(&kmac_key, &kek);
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t result = OK_STATUS();

  CHECK_STATUS_OK(entropy_complex_init());
  EXECUTE_TEST(result, wrap_unwrap_random_test);

  return status_ok(result);
}
