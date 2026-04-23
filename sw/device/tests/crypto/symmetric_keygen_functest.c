// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/drivers/keymgr.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/drbg.h"
#include "sw/device/lib/crypto/include/entropy_src.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/key_transport.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/keymgr_testutils.h"
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

// Represents a 192-bit AES-CBC key.
static otcrypto_key_config_t kAesKeyConfig = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeAesCbc,
    .key_length = 192 / 8,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

// Represents a 256-bit HMAC-SHA256 key.
static otcrypto_key_config_t kHmacKeyConfig = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeHmacSha256,
    .key_length = 256 / 8,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

// Represents a 128-bit KMAC key.
static otcrypto_key_config_t kKmacKeyConfig = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeKmac128,
    .key_length = 128 / 8,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

/**
 * Basic test for generating a symmetric key.
 *
 * Generates the key, runs basic statistical tests, and logs the output. This
 * test may fail sometimes because statistical tests are inherently
 * proababilistic.
 *
 * @param config Key configuration.
 */
static status_t basic_keygen_test(otcrypto_key_config_t config) {
  // Personalization data for testing.
  uint8_t kPersonalizationData[5] = {0xf0, 0xf1, 0xf2, 0xf3, 0xf4};
  otcrypto_const_byte_buf_t kPersonalization =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, kPersonalizationData,
                        sizeof(kPersonalizationData));

  // Allocate and zeroize keyblob.
  size_t key_share_words = config.key_length / sizeof(uint32_t);
  uint32_t keyblob[key_share_words * 2];
  memset(keyblob, 0, sizeof(keyblob));

  // Create the blinded key structure and call keygen.
  otcrypto_blinded_key_t key = {
      .config = config,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  TRY(otcrypto_symmetric_keygen(&kPersonalization, &key));

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
  // Personalization data for testing.
  uint8_t kPersonalizationData[5] = {0xf0, 0xf1, 0xf2, 0xf3, 0xf4};
  otcrypto_const_byte_buf_t kPersonalization =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, kPersonalizationData,
                        sizeof(kPersonalizationData));
  // Create a double-length blob for two keys.
  size_t key_share_words = kAesKeyConfig.key_length / sizeof(uint32_t);
  uint32_t keyblob_buffer[key_share_words * 4];
  uint32_t *keyblob1 = keyblob_buffer;
  uint32_t *keyblob2 = &keyblob_buffer[key_share_words * 2];
  memset(keyblob_buffer, 0, sizeof(keyblob_buffer));

  // Generate two AES keys.
  otcrypto_blinded_key_t key1 = {
      .config = kAesKeyConfig,
      .keyblob_length = sizeof(keyblob_buffer) / 2,
      .keyblob = keyblob1,
  };
  otcrypto_blinded_key_t key2 = {
      .config = kAesKeyConfig,
      .keyblob_length = sizeof(keyblob_buffer) / 2,
      .keyblob = keyblob2,
  };
  TRY(otcrypto_symmetric_keygen(&kPersonalization, &key1));
  TRY(otcrypto_symmetric_keygen(&kPersonalization, &key2));

  // Do a statistical test on the entire keyblob (this will check if the keys
  // are statistically related to each other).
  TRY(randomness_quality_monobit_test((unsigned char *)keyblob_buffer,
                                      sizeof(keyblob_buffer), kSignificance));

  return OK_STATUS();
}

/**
 * Test for deriving a hardware-backed software-visible key.
 */
static status_t hw_backed_keygen_test(void) {
  // Configuration for a 256-bit hardware-backed key.
  otcrypto_key_config_t config = {
      .version = kOtcryptoLibVersion1,
      // the .mode can be any value
      .key_length = 256 / 8,
      .hw_backed = kHardenedBoolTrue,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };

  // The final software-visible key generated by the key manager has two
  // 8-word shares.
  uint32_t keyblob[16];
  memset(keyblob, 0, sizeof(keyblob));

  otcrypto_blinded_key_t key = {
      .config = config,
      .keyblob_length = 8 * sizeof(uint32_t),
      .keyblob = keyblob,
  };

  // Version allowed by the key manager.
  uint32_t version = 0;
  // Example salt.
  const uint32_t salt[7] = {0x11111111, 0x22222222, 0x33333333, 0x44444444,
                            0x55555555, 0x66666666, 0x77777777};

  // Initialize the hardware-backed keyblob preset.
  TRY(otcrypto_hw_backed_key(version, salt, &key));
  TRY_CHECK(key.checksum == integrity_blinded_checksum(&key));

  // Generate the SW-visible key from the hardware-backed preset.
  TRY(ot_crypto_hw_backed_keygen(kHardenedBoolFalse, &key));

  // Verify the key struct was morphed correctly.
  TRY_CHECK(key.config.hw_backed == kHardenedBoolFalse);
  TRY_CHECK(key.keyblob_length == 16 * sizeof(uint32_t));
  TRY_CHECK(integrity_blinded_key_check(&key) == kHardenedBoolTrue);

  return OK_STATUS();
}

static status_t test_setup(void) {
  // Initialize the key manager and advance to OwnerRootKey state.  Note: the
  // keymgr testutils set this up using software entropy, so there is no need
  // to initialize the entropy complex first. However, this is of course not
  // the expected setup in production.
  dif_keymgr_t keymgr;
  dif_kmac_t kmac;
  dif_keymgr_state_t keymgr_state;
  TRY(keymgr_testutils_try_startup(&keymgr, &kmac, &keymgr_state));

  if (keymgr_state == kDifKeymgrStateCreatorRootKey) {
    TRY(keymgr_testutils_advance_state(&keymgr, &kOwnerIntParams));
    TRY(keymgr_testutils_advance_state(&keymgr, &kOwnerRootKeyParams));
  } else if (keymgr_state == kDifKeymgrStateOwnerIntermediateKey) {
    TRY(keymgr_testutils_advance_state(&keymgr, &kOwnerRootKeyParams));
  }

  TRY(keymgr_testutils_check_state(&keymgr, kDifKeymgrStateOwnerRootKey));

  // Initialize entropy complex for cryptolib, which the key manager uses to
  // clear sideloaded keys. The `keymgr_testutils_startup` function restarts
  // the device, so this should happen afterwards.
  return otcrypto_init(kOtcryptoKeySecurityLevelLow);
}

bool test_main(void) {
  status_t result = OK_STATUS();

  EXECUTE_TEST(result, test_setup);

  EXECUTE_TEST(result, aes_keygen_test);
  EXECUTE_TEST(result, hmac_keygen_test);
  EXECUTE_TEST(result, kmac_keygen_test);
  EXECUTE_TEST(result, generate_multiple_keys_test);
  EXECUTE_TEST(result, hw_backed_keygen_test);
  return status_ok(result);
}
