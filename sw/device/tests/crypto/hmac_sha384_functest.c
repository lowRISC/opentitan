// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/mac.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

enum {
  /**
   * HMAC-SHA384 tag length (384 bits) in words.
   */
  kTagLenWords = 384 / 32,
};

// Randomly generated 384-bit test key (big endian) =
// 0x7751ae57bc0ba74f9d5cba1a458d9543342c70fe102f5e2fb339c2500f5610f132276a7cb87d39cde522efea6ba18dd1
static const uint32_t kBasicTestKey[] = {
    0x57ae5177, 0x4fa70bbc, 0x1aba5c9d, 0x43958d45, 0xfe702c34, 0x2f5e2f10,
    0x50c239b3, 0xf110560f, 0x7c6a2732, 0xcd397db8, 0xeaef22e5, 0xd18da16b};

// Test key longer than the message block size, 1088 bits (big endian) =
// 0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f40414243000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f40414243
static const uint32_t kLongTestKey[] = {
    0x03020100, 0x07060504, 0x0b0a0908, 0x0f0e0d0c, 0x13121110, 0x17161514,
    0x1b1a1918, 0x1f1e1d1c, 0x23222120, 0x27262524, 0x2b2a2928, 0x2f2e2d2c,
    0x33323130, 0x37363534, 0x3b3a3938, 0x3f3e3d3c, 0x43424140, 0x03020100,
    0x07060504, 0x0b0a0908, 0x0f0e0d0c, 0x13121110, 0x17161514, 0x1b1a1918,
    0x1f1e1d1c, 0x23222120, 0x27262524, 0x2b2a2928, 0x2f2e2d2c, 0x33323130,
    0x37363534, 0x3b3a3938, 0x3f3e3d3c, 0x43424140,
};

// Random value for masking, as large as the longest test key. This value
// should not affect the result.
static const uint32_t kTestMask[ARRAYSIZE(kLongTestKey)] = {
    0x8cb847c3, 0xc6d34f36, 0x72edbf7b, 0x9bc0317f, 0x8f003c7f, 0x1d7ba049,
    0xfd463b63, 0xbb720c44, 0x784c215e, 0xeb101d65, 0x35beb911, 0xab481345,
    0xa7ebc3e3, 0x04b2a1b9, 0x764a9630, 0x78b8f9c5, 0x3f2a1d8e, 0x8cb847c3,
    0xc6d34f36, 0x72edbf7b, 0x9bc0317f, 0x8f003c7f, 0x1d7ba049, 0xfd463b63,
    0xbb720c44, 0x784c215e, 0xeb101d65, 0x35beb911, 0xab481345, 0xa7ebc3e3,
    0x04b2a1b9, 0x764a9630, 0x78b8f9c5, 0x3f2a1d8e,
};

/**
 * Call the `otcrypto_mac` API and check the resulting tag.
 *
 * @param key Key material.
 * @param key_num_words Key length in bytes.
 * @param msg Input message.
 * @param exp_tag Expected tag.
 * @return Result (OK or error).
 */
static status_t run_test(const uint32_t *key, size_t key_len,
                         crypto_const_byte_buf_t msg, const uint32_t *exp_tag) {
  // Construct blinded key.
  crypto_key_config_t config = {
      .version = kCryptoLibVersion1,
      .key_mode = kKeyModeHmacSha384,
      .key_length = key_len,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kSecurityLevelLow,
  };

  uint32_t keyblob[keyblob_num_words(config)];
  TRY(keyblob_from_key_and_mask(key, kTestMask, config, keyblob));
  crypto_blinded_key_t blinded_key = {
      .config = config,
      .keyblob = keyblob,
      .keyblob_length = sizeof(keyblob),
      .checksum = 0,
  };
  blinded_key.checksum = integrity_blinded_checksum(&blinded_key);

  uint32_t act_tag[kTagLenWords];
  crypto_word32_buf_t tag_buf = {
      .data = act_tag,
      .len = ARRAYSIZE(act_tag),
  };

  TRY(otcrypto_hmac(&blinded_key, msg, kHashModeSha384, &tag_buf));
  TRY_CHECK_ARRAYS_EQ(act_tag, exp_tag, kTagLenWords);
  return OK_STATUS();
}

/**
 * Simple test with a short message.
 *
 * HMAC-SHA384(kBasicTestKey, 'Test message.')
 *   =
 * 0x2fba69e09ba15197aff88d3768aaee009cb6895763c31dcdf1d0146d4e4462d01a3c68ed42e6cee1e67b4ba48bdd1805
 */
static status_t simple_test(void) {
  const char plaintext[] = "Test message.";
  crypto_const_byte_buf_t msg_buf = {
      .data = (unsigned char *)plaintext,
      .len = sizeof(plaintext) - 1,
  };
  const uint32_t exp_tag[] = {
      0xe069ba2f, 0x9751a19b, 0x378df8af, 0x00eeaa68, 0x5789b69c, 0xcd1dc363,
      0x6d14d0f1, 0xd062444e, 0xed683c1a, 0xe1cee642, 0xa44b7be6, 0x0518dd8b,
  };
  return run_test(kBasicTestKey, sizeof(kBasicTestKey), msg_buf, exp_tag);
}

/**
 * Test with an empty message.
 *
 * HMAC-SHA384(kBasicTestKey, '')
 * =
 * 0xb69271e94f5f5da40337cdb2f2d3412b6d568b7b51a86f7109f8454f3c34276cf44a5b98997ce3ab8f59170b6e1f71f9
 */
static status_t empty_test(void) {
  const uint32_t exp_tag[] = {
      0xe97192b6, 0xa45d5f4f, 0xb2cd3703, 0x2b41d3f2, 0x7b8b566d, 0x716fa851,
      0x4f45f809, 0x6c27343c, 0x985b4af4, 0xabe37c99, 0x0b17598f, 0xf9711f6e,
  };
  crypto_const_byte_buf_t msg_buf = {
      .data = NULL,
      .len = 0,
  };
  return run_test(kBasicTestKey, sizeof(kBasicTestKey), msg_buf, exp_tag);
}

/**
 * Test using a long key.
 *
 * HMAC-SHA384(kLongTestKey, 'Test message.')
 *   =
 * 0xaacc6a2d9aadee928c78467c02a881b00afc8a6b004d09cf05b8a492651a5f5cf8d4bc988598b2bd3154f07239b48dc0
 */
static status_t long_key_test(void) {
  const char plaintext[] = "Test message.";
  crypto_const_byte_buf_t msg_buf = {
      .data = (unsigned char *)plaintext,
      .len = sizeof(plaintext) - 1,
  };
  const uint32_t exp_tag[] = {
      0x2d6accaa, 0x92eead9a, 0x7c46788c, 0xb081a802, 0x6b8afc0a, 0xcf094d00,
      0x92a4b805, 0x5c5f1a65, 0x98bcd4f8, 0xbdb29885, 0x72f05431, 0xc08db439,
  };
  return run_test(kLongTestKey, sizeof(kLongTestKey), msg_buf, exp_tag);
}

OTTF_DEFINE_TEST_CONFIG();

// Holds the test result.
static volatile status_t test_result;

bool test_main(void) {
  test_result = OK_STATUS();
  EXECUTE_TEST(test_result, empty_test);
  EXECUTE_TEST(test_result, simple_test);
  EXECUTE_TEST(test_result, long_key_test);
  return status_ok(test_result);
}
