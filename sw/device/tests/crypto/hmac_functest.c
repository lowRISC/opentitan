// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/hmac.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/mac.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// Test key (big endian) =
// 0x1bff10eaa5b9b204d6f3232a573e8e51a27b68c319366deaf26b91b0712f7a34
static const hmac_key_t kTestKey = {
    .key =
        {
            0x1bff10ea,
            0xa5b9b204,
            0xd6f3232a,
            0x573e8e51,
            0xa27b68c3,
            0x19366dea,
            0xf26b91b0,
            0x712f7a34,
        },
};

// Random value for masking (should not affect result).
static const uint32_t kTestMask[kHmacKeyNumWords] = {
    0x8cb847c3, 0xc6d34f36, 0x72edbf7b, 0x9bc0317f,
    0x8f003c7f, 0x1d7ba049, 0xfd463b63, 0xbb720c44,
};

/**
 * Call the `otcrypto_mac` API and check the resulting tag.
 *
 * @param msg Input message.
 * @param exp_tag Expected tag (256 bits).
 */
static void run_test(crypto_const_uint8_buf_t msg, const uint32_t *exp_tag) {
  // Construct blinded key.
  crypto_key_config_t config = {
      .version = kCryptoLibVersion1,
      .key_mode = kKeyModeHmacSha256,
      .key_length = kHmacKeyNumBytes,
      .hw_backed = kHardenedBoolFalse,
      .diversification_hw_backed = {.data = NULL, .len = 0},
      .exportable = kHardenedBoolFalse,
      .security_level = kSecurityLevelLow,
  };

  uint32_t keyblob[keyblob_num_words(config)];
  CHECK_STATUS_OK(
      keyblob_from_key_and_mask(kTestKey.key, kTestMask, config, keyblob));
  crypto_blinded_key_t blinded_key = {
      .config = config,
      .keyblob = keyblob,
      .keyblob_length = sizeof(keyblob),
      .checksum = 0,
  };
  blinded_key.checksum = integrity_blinded_checksum(&blinded_key);

  uint32_t act_tag[kHmacDigestNumWords];
  crypto_uint8_buf_t tag_buf = {
      .data = (unsigned char *)act_tag,
      .len = sizeof(act_tag),
  };

  crypto_status_t status = otcrypto_hmac(&blinded_key, msg, &tag_buf);
  CHECK(status == kCryptoStatusOK, "Error during hmac operation: 0x%08x.",
        status);
  CHECK_ARRAYS_EQ(act_tag, exp_tag, kHmacDigestNumWords);
}

/**
 * Simple test with a short message.
 *
 * HMAC-SHA256(kTestKey, 'Test message.')
 *   = 0xb4595b02be2a1638893166366656ece12b749b95a2815e52d687535309f3126f
 */
static void simple_test(void) {
  const char plaintext[] = "Test message.";
  crypto_const_uint8_buf_t msg_buf = {
      .data = (unsigned char *)plaintext,
      .len = sizeof(plaintext) - 1,
  };
  const uint32_t exp_tag[kHmacDigestNumWords] = {
      0x09f3126f, 0xd6875353, 0xa2815e52, 0x2b749b95,
      0x6656ece1, 0x89316636, 0xbe2a1638, 0xb4595b02,
  };
  run_test(msg_buf, exp_tag);
}

/**
 * Test with an empty message.
 *
 * HMAC-SHA256(kTestKey, '')
 * = 0xa9425cbb40d13a0e07916761c06c4aa37969305361508afae62e8bbca5c099a4
 */
static void empty_test(void) {
  const uint32_t exp_tag[kHmacDigestNumWords] = {
      0xa5c099a4, 0xe62e8bbc, 0x61508afa, 0x79693053,
      0xc06c4aa3, 0x07916761, 0x40d13a0e, 0xa9425cbb,
  };
  crypto_const_uint8_buf_t msg_buf = {
      .data = NULL,
      .len = 0,
  };
  run_test(msg_buf, exp_tag);
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  simple_test();
  empty_test();

  return true;
}
