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
   * HMAC-SHA512 tag length (512 bits) in words.
   */
  kTagLenWords = 512 / 32,
};

// Randomly generated 512-bit test key (big endian) =
// 0xba79877bb2027c689bef5c69567ca099977928d90a82c05c5d18c39967d4099f64b9f8d7dd192cd6e5902fb599fb601a6879ecb0fdb081bf1b75a4c1ed8865a4
static const uint32_t kBasicTestKey[] = {
    0x7b8779ba, 0x687c02b2, 0x695cef9b, 0x99a07c56, 0xd9287997, 0x5cc0820a,
    0x99c3185d, 0x9f09d467, 0xd7f8b964, 0xd62c19dd, 0xb52f90e5, 0x1a60fb99,
    0xb0ec7968, 0xbf81b0fd, 0xc1a4751b, 0xa46588ed,

};

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
      .key_mode = kKeyModeHmacSha512,
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

  TRY(otcrypto_hmac(&blinded_key, msg, kHashModeSha512, &tag_buf));
  TRY_CHECK_ARRAYS_EQ(act_tag, exp_tag, kTagLenWords);
  return OK_STATUS();
}

/**
 * Simple test with a short message.
 *
 * HMAC-SHA512(kBasicTestKey, 'Test message.')
 *   =
 * 0xa574367b4c84120c0bef3a2e0c5675b86fe0f21f980cc82cfe21b63442d3d12a2d33377a6471d9167eb9b3155543273bac2146e26208c95dc3490727417802ba
 */
static status_t simple_test(void) {
  const char plaintext[] = "Test message.";
  crypto_const_byte_buf_t msg_buf = {
      .data = (unsigned char *)plaintext,
      .len = sizeof(plaintext) - 1,
  };
  const uint32_t exp_tag[] = {
      0x7b3674a5, 0x0c12844c, 0x2e3aef0b, 0xb875560c, 0x1ff2e06f, 0x2cc80c98,
      0x34b621fe, 0x2ad1d342, 0x7a37332d, 0x16d97164, 0x15b3b97e, 0x3b274355,
      0xe24621ac, 0x5dc90862, 0x270749c3, 0xba027841,

  };
  return run_test(kBasicTestKey, sizeof(kBasicTestKey), msg_buf, exp_tag);
}

/**
 * Test with an empty message.
 *
 * HMAC-SHA512(kBasicTestKey, '')
 *   =
 * 0xef725f225b5c7e880aabfb5c3dd6d8d5f3027aaf1a532e502f65e48a1c9196cff712e44f3b2700d9c02321a363b7b9c51a598b9226a737704a6d19dff79c582d
 */
static status_t empty_test(void) {
  const uint32_t exp_tag[] = {
      0x225f72ef, 0x887e5c5b, 0x5cfbab0a, 0xd5d8d63d, 0xaf7a02f3, 0x502e531a,
      0x8ae4652f, 0xcf96911c, 0x4fe412f7, 0xd900273b, 0xa32123c0, 0xc5b9b763,
      0x928b591a, 0x7037a726, 0xdf196d4a, 0x2d589cf7,

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
 * HMAC-SHA512(kLongTestKey, 'Test message.')
 *   =
 * 0x6f18c6e54d2498dfd73bd6e04b38a85d2c94fcfc2ac7e54ea2eb5884a8e4ebb0a5e0954f7ec5fdc26b3c15aed8706620d72d97a3f0b986b631b2d550249c724d
 */
static status_t long_key_test(void) {
  const char plaintext[] = "Test message.";
  crypto_const_byte_buf_t msg_buf = {
      .data = (unsigned char *)plaintext,
      .len = sizeof(plaintext) - 1,
  };
  const uint32_t exp_tag[] = {
      0xe5c6186f, 0xdf98244d, 0xe0d63bd7, 0x5da8384b, 0xfcfc942c, 0x4ee5c72a,
      0x8458eba2, 0xb0ebe4a8, 0x4f95e0a5, 0xc2fdc57e, 0xae153c6b, 0x206670d8,
      0xa3972dd7, 0xb686b9f0, 0x50d5b231, 0x4d729c24,

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
