// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/mac.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

enum {
  /**
   * HMAC-SHA256 tag length (256 bits) in words.
   */
  kTagLenWords = 256 / 32,
};

// 256-bit test key (big endian) =
// 0x1bff10eaa5b9b204d6f3232a573e8e51a27b68c319366deaf26b91b0712f7a34
static const uint32_t kBasicTestKey[] = {
    0xea10ff1b, 0x04b2b9a5, 0x2a23f3d6, 0x518e3e57,
    0xc3687ba2, 0xea6d3619, 0xb0916bf2, 0x347a2f71,
};

// Long test key, 544 bits (big endian) =
// 0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f40414243
static const uint32_t kLongTestKey[] = {
    0x03020100, 0x07060504, 0x0b0a0908, 0x0f0e0d0c, 0x13121110, 0x17161514,
    0x1b1a1918, 0x1f1e1d1c, 0x23222120, 0x27262524, 0x2b2a2928, 0x2f2e2d2c,
    0x33323130, 0x37363534, 0x3b3a3938, 0x3f3e3d3c, 0x43424140,
};

// Random value for masking, as large as the longest test key. This value
// should not affect the result.
static const uint32_t kTestMask[ARRAYSIZE(kLongTestKey)] = {
    0x8cb847c3, 0xc6d34f36, 0x72edbf7b, 0x9bc0317f, 0x8f003c7f, 0x1d7ba049,
    0xfd463b63, 0xbb720c44, 0x784c215e, 0xeb101d65, 0x35beb911, 0xab481345,
    0xa7ebc3e3, 0x04b2a1b9, 0x764a9630, 0x78b8f9c5, 0x3f2a1d8e,
};

/**
 * Call the `otcrypto_mac` API and check the resulting tag.
 *
 * @param key Key material.
 * @param key_num_words Key length in bytes.
 * @param msg Input message.
 * @param exp_tag Expected tag (256 bits).
 * @return Result (OK or error).
 */
static status_t run_test(const uint32_t *key, size_t key_len,
                         otcrypto_const_byte_buf_t msg,
                         const uint32_t *exp_tag) {
  // Construct blinded key.
  otcrypto_key_config_t config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeHmacSha256,
      .key_length = key_len,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };

  uint32_t keyblob[keyblob_num_words(config)];
  TRY(keyblob_from_key_and_mask(key, kTestMask, config, keyblob));
  otcrypto_blinded_key_t blinded_key = {
      .config = config,
      .keyblob = keyblob,
      .keyblob_length = sizeof(keyblob),
      .checksum = 0,
  };
  blinded_key.checksum = integrity_blinded_checksum(&blinded_key);

  uint32_t act_tag[kTagLenWords];
  otcrypto_word32_buf_t tag_buf = {
      .data = act_tag,
      .len = ARRAYSIZE(act_tag),
  };

  TRY(otcrypto_hmac(&blinded_key, msg, tag_buf));
  TRY_CHECK_ARRAYS_EQ(act_tag, exp_tag, kTagLenWords);
  return OK_STATUS();
}

/**
 * Simple test with a short message.
 *
 * HMAC-SHA256(kBasicTestKey, 'Test message.')
 *   = 0xb4595b02be2a1638893166366656ece12b749b95a2815e52d687535309f3126f
 */
static status_t simple_test(void) {
  const char plaintext[] = "Test message.";
  otcrypto_const_byte_buf_t msg_buf = {
      .data = (unsigned char *)plaintext,
      .len = sizeof(plaintext) - 1,
  };
  const uint32_t exp_tag[] = {
      0x025b59b4, 0x38162abe, 0x36663189, 0xe1ec5666,
      0x959b742b, 0x525e81a2, 0x535387d6, 0x6f12f309,
  };
  return run_test(kBasicTestKey, sizeof(kBasicTestKey), msg_buf, exp_tag);
}

/**
 * Test with an empty message.
 *
 * HMAC-SHA256(kBasicTestKey, '')
 * = 0xa9425cbb40d13a0e07916761c06c4aa37969305361508afae62e8bbca5c099a4
 */
static status_t empty_test(void) {
  const uint32_t exp_tag[] = {
      0xbb5c42a9, 0x0e3ad140, 0x61679107, 0xa34a6cc0,
      0x53306979, 0xfa8a5061, 0xbc8b2ee6, 0xa499c0a5,
  };
  otcrypto_const_byte_buf_t msg_buf = {
      .data = NULL,
      .len = 0,
  };
  return run_test(kBasicTestKey, sizeof(kBasicTestKey), msg_buf, exp_tag);
}

/**
 * Test using a long key.
 *
 * HMAC-SHA256(kLongTestKey, 'Test message.')
 *   = 0x6fab77a49de1fa73dfa97f4f36b956d552afd11d77f584cd8c5c8332d32a6836
 */
static status_t long_key_test(void) {
  const char plaintext[] = "Test message.";
  otcrypto_const_byte_buf_t msg_buf = {
      .data = (unsigned char *)plaintext,
      .len = sizeof(plaintext) - 1,
  };
  const uint32_t exp_tag[] = {
      0xa477ab6f, 0x73fae19d, 0x4f7fa9df, 0xd556b936,
      0x1dd1af52, 0xcd84f577, 0x32835c8c, 0x36682ad3,
  };
  return run_test(kLongTestKey, sizeof(kLongTestKey), msg_buf, exp_tag);
}

OTTF_DEFINE_TEST_CONFIG();

// Holds the test result.
static volatile status_t test_result;

bool test_main(void) {
  test_result = OK_STATUS();
  CHECK_STATUS_OK(entropy_complex_init());
  EXECUTE_TEST(test_result, simple_test);
  EXECUTE_TEST(test_result, empty_test);
  EXECUTE_TEST(test_result, long_key_test);
  return status_ok(test_result);
}
