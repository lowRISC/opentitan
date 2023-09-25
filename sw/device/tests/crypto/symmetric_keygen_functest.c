// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/drbg.h"
#include "sw/device/lib/crypto/include/key_transport.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/randomness_quality.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

OTTF_DEFINE_TEST_CONFIG();

// Statistical significance for randomness-quality checks. This setting results
// in a 1% failure rate on truly random data.
static const randomness_quality_significance_t kSignificance =
    kRandomnessQualitySignificanceOnePercent;

// Personalization data for testing.
static const uint8_t kPersonalizationData[5] = {0xf0, 0xf1, 0xf2, 0xf3, 0xf4};
static const crypto_const_byte_buf_t kPersonalization = {
    .data = kPersonalizationData,
    .len = sizeof(kPersonalizationData),
};

// Represents a 192-bit AES-CBC key.
static const crypto_key_config_t kAesKeyConfig = {
    .version = kCryptoLibVersion1,
    .key_mode = kKeyModeAesCbc,
    .key_length = 192 / 8,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kSecurityLevelLow,
};

// Represents a 256-bit HMAC-SHA256 key.
static const crypto_key_config_t kHmacKeyConfig = {
    .version = kCryptoLibVersion1,
    .key_mode = kKeyModeHmacSha256,
    .key_length = 256 / 8,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kSecurityLevelLow,
};

// Represents a 128-bit KMAC key.
static const crypto_key_config_t kKmacKeyConfig = {
    .version = kCryptoLibVersion1,
    .key_mode = kKeyModeKmac128,
    .key_length = 128 / 8,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kSecurityLevelLow,
};

static status_t entropy_complex_init_test(void) {
  // This initialization should happen in ROM_EXT, so there is no public API
  // for it in cryptolib.
  TRY(entropy_complex_init());

  // Check the configuration.
  return entropy_complex_check();
}

/**
 * Basic test for generating a symmetric key.
 *
 * Generates the key, runs basic statistical tests, and logs the output. This
 * test may fail sometimes because statistical tests are inherently
 * proababilistic.
 *
 * @param config Key configuration.
 */
static status_t basic_keygen_test(crypto_key_config_t config) {
  // Allocate and zeroize keyblob.
  size_t key_share_words = config.key_length / sizeof(uint32_t);
  uint32_t keyblob[key_share_words * 2];
  memset(keyblob, 0, sizeof(keyblob));

  // Create the blinded key structure and call keygen.
  crypto_blinded_key_t key = {
      .config = config,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  TRY(otcrypto_symmetric_keygen(kPersonalization, &key));

  // Ensure the checksum passes.
  TRY_CHECK(integrity_blinded_key_check(&key) == kHardenedBoolTrue);

  // Do a basic statistical test.
  TRY(randomness_quality_monobit_test((unsigned char *)keyblob, sizeof(keyblob),
                                      kSignificance));

  // Log the generated key.
  uint32_t *share0;
  uint32_t *share1;
  HARDENED_TRY(keyblob_to_shares(&key, &share0, &share1));
  for (size_t i = 0; i < key_share_words; i++) {
    LOG_INFO("key[%d] = 0x%08x", i, share0[i] ^ share1[i]);
  }

  return OK_STATUS();
}

static status_t aes_keygen_test(void) {
  return basic_keygen_test(kAesKeyConfig);
}

static status_t hmac_keygen_test(void) {
  return basic_keygen_test(kHmacKeyConfig);
}

static status_t kmac_keygen_test(void) {
  return basic_keygen_test(kKmacKeyConfig);
}

static status_t generate_multiple_keys_test(void) {
  // Create a double-length blob for two keys.
  size_t key_share_words = kAesKeyConfig.key_length / sizeof(uint32_t);
  uint32_t keyblob_buffer[key_share_words * 4];
  uint32_t *keyblob1 = keyblob_buffer;
  uint32_t *keyblob2 = &keyblob_buffer[key_share_words * 2];
  memset(keyblob_buffer, 0, sizeof(keyblob_buffer));

  // Generate two AES keys.
  crypto_blinded_key_t key1 = {
      .config = kAesKeyConfig,
      .keyblob_length = sizeof(keyblob_buffer) / 2,
      .keyblob = keyblob1,
  };
  crypto_blinded_key_t key2 = {
      .config = kAesKeyConfig,
      .keyblob_length = sizeof(keyblob_buffer) / 2,
      .keyblob = keyblob2,
  };
  TRY(otcrypto_symmetric_keygen(kPersonalization, &key1));
  TRY(otcrypto_symmetric_keygen(kPersonalization, &key2));

  // Do a statistical test on the entire keyblob (this will check if the keys
  // are statistically related to each other).
  TRY(randomness_quality_monobit_test((unsigned char *)keyblob_buffer,
                                      sizeof(keyblob_buffer), kSignificance));

  return OK_STATUS();
}

bool test_main(void) {
  status_t result = OK_STATUS();

  EXECUTE_TEST(result, entropy_complex_init_test);
  EXECUTE_TEST(result, aes_keygen_test);
  EXECUTE_TEST(result, hmac_keygen_test);
  EXECUTE_TEST(result, kmac_keygen_test);
  EXECUTE_TEST(result, generate_multiple_keys_test);
  return status_ok(result);
}
