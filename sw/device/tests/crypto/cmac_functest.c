// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/cmac.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/entropy_src.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/crypto/lib/crypto_test_lib.h"

enum {
  /**
   * CMAC tag length (128 bits) in words.
   */
  kTagLenWords = 128 / 32,
};

// RFC 4493 AES-128 CMAC Test Key
// Key: 2b7e1516 28aed2a6 abf71588 09cf4f3c
static const uint32_t kAes128TestKey[] = {
    0x16157e2b,
    0xa6d2ae28,
    0x8815f7ab,
    0x3c4fcf09,
};

// Random value for masking, as large as an AES-256 key.
// This value should not affect the result.
static const uint32_t kTestMask[8] = {
    0x8cb847c3, 0xc6d34f36, 0x72edbf7b, 0x9bc0317f,
    0x8f003c7f, 0x1d7ba049, 0xfd463b63, 0xbb720c44,
};

static otcrypto_key_security_level_t current_sec_level =
    kOtcryptoKeySecurityLevelLow;

/**
 * Call the `otcrypto_cmac` API and check the resulting tag.
 *
 * @param key Key material.
 * @param key_len Key length in bytes.
 * @param msg Input message.
 * @param exp_tag Expected tag (128 bits).
 * @return Result (OK or error).
 */
static status_t run_test(const uint32_t *key, size_t key_len,
                         otcrypto_const_byte_buf_t msg,
                         const uint32_t *exp_tag) {
  // Construct blinded key.
  otcrypto_key_config_t config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeAesCmac,
      .key_length = key_len,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = current_sec_level,
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
  otcrypto_word32_buf_t tag_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, act_tag, ARRAYSIZE(act_tag));

  TRY(otcrypto_cmac(&blinded_key, &msg, &tag_buf));
  TRY_CHECK_ARRAYS_EQ(act_tag, exp_tag, kTagLenWords);
  return OK_STATUS();
}

/**
 * Test with an empty message.
 *
 * CMAC(kAes128TestKey, '')
 * = bb1d6929 e9593728 7fa37d12 9b756746
 */
static status_t empty_test(void) {
  const uint32_t exp_tag[] = {
      0x29691dbb,
      0x283759e9,
      0x127da37f,
      0x4667759b,
  };
  otcrypto_const_byte_buf_t msg_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 0);
  return run_test(kAes128TestKey, sizeof(kAes128TestKey), msg_buf, exp_tag);
}

/**
 * Simple test with exactly one block (16 bytes).
 *
 * CMAC(kAes128TestKey, '6bc1bee2 2e409f96 e93d7e11 7393172a')
 * = 070a16b4 6b4d4144 f79bdd9d d04a287c
 */
static status_t one_block_test(void) {
  const uint8_t msg[] = {
      0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96,
      0xe9, 0x3d, 0x7e, 0x11, 0x73, 0x93, 0x17, 0x2a,
  };
  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, (unsigned char *)msg, sizeof(msg));
  const uint32_t exp_tag[] = {
      0xb4160a07,
      0x44414d6b,
      0x9ddd9bf7,
      0x7c284ad0,
  };
  return run_test(kAes128TestKey, sizeof(kAes128TestKey), msg_buf, exp_tag);
}

/**
 * Test using multiple blocks with a partial final block (40 bytes total).
 *
 * CMAC(kAes128TestKey, '6bc1...e411')
 * = dfa66747 de9ae630 30ca3261 1497c827
 */
static status_t multi_block_test(void) {
  const uint8_t msg[] = {
      0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96, 0xe9, 0x3d,
      0x7e, 0x11, 0x73, 0x93, 0x17, 0x2a, 0xae, 0x2d, 0x8a, 0x57,
      0x1e, 0x03, 0xac, 0x9c, 0x9e, 0xb7, 0x6f, 0xac, 0x45, 0xaf,
      0x8e, 0x51, 0x30, 0xc8, 0x1c, 0x46, 0xa3, 0x5c, 0xe4, 0x11,
  };
  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, (unsigned char *)msg, sizeof(msg));
  const uint32_t exp_tag[] = {
      0x4767a6df,
      0x30e69ade,
      0x6132ca30,
      0x27c89714,
  };
  return run_test(kAes128TestKey, sizeof(kAes128TestKey), msg_buf, exp_tag);
}

/**
 * Simple streaming test.
 *
 * CMAC(kAes128TestKey, '6bc1...e411')
 * = dfa66747 de9ae630 30ca3261 1497c827
 */
static status_t streaming_test(void) {
  const uint8_t msg[] = {
      0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96, 0xe9, 0x3d,
      0x7e, 0x11, 0x73, 0x93, 0x17, 0x2a, 0xae, 0x2d, 0x8a, 0x57,
      0x1e, 0x03, 0xac, 0x9c, 0x9e, 0xb7, 0x6f, 0xac, 0x45, 0xaf,
      0x8e, 0x51, 0x30, 0xc8, 0x1c, 0x46, 0xa3, 0x5c, 0xe4, 0x11,
  };
  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, (unsigned char *)msg, sizeof(msg));
  const uint32_t exp_tag[] = {
      0x4767a6df,
      0x30e69ade,
      0x6132ca30,
      0x27c89714,
  };

  // Construct blinded key.
  otcrypto_key_config_t config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeAesCmac,
      .key_length = sizeof(kAes128TestKey),
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = current_sec_level,
  };

  uint32_t keyblob[keyblob_num_words(config)];
  TRY(keyblob_from_key_and_mask(kAes128TestKey, kTestMask, config, keyblob));
  otcrypto_blinded_key_t blinded_key = {
      .config = config,
      .keyblob = keyblob,
      .keyblob_length = sizeof(keyblob),
      .checksum = 0,
  };
  blinded_key.checksum = integrity_blinded_checksum(&blinded_key);

  uint32_t act_tag[kTagLenWords];
  otcrypto_word32_buf_t tag_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, act_tag, ARRAYSIZE(act_tag));

  // First, try using the streaming interface but passing input all at once.
  otcrypto_cmac_context_t ctx;
  TRY(otcrypto_cmac_init(&ctx, &blinded_key));
  TRY(otcrypto_cmac_update(&ctx, &msg_buf));
  TRY(otcrypto_cmac_final(&ctx, &tag_buf));
  TRY_CHECK_ARRAYS_EQ(act_tag, exp_tag, kTagLenWords);

  // Clear the destination buffer.
  memset(act_tag, 0, sizeof(act_tag));

  // Next, try processing in chunk sizes unaligned to the block length (e.g. 7
  // bytes).
  size_t chunk_size = 7;
  const unsigned char *msg_bytes = msg_buf.data;
  size_t msg_len = msg_buf.len;

  TRY(otcrypto_cmac_init(&ctx, &blinded_key));
  size_t offset = 0;
  for (; offset + chunk_size < msg_len; offset += chunk_size) {
    otcrypto_const_byte_buf_t msg_chunk =
        OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, msg_bytes, chunk_size);
    TRY(otcrypto_cmac_update(&ctx, &msg_chunk));
    msg_bytes += chunk_size;
  }

  // One final update for any remaining data.
  otcrypto_const_byte_buf_t msg_final_buffer = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, (unsigned char *)msg_bytes, msg_len - offset);
  TRY(otcrypto_cmac_update(&ctx, &msg_final_buffer));
  TRY(otcrypto_cmac_final(&ctx, &tag_buf));

  TRY_CHECK_ARRAYS_EQ(act_tag, exp_tag, kTagLenWords);
  return OK_STATUS();
}

OTTF_DEFINE_TEST_CONFIG();

// Holds the test result.
static volatile status_t test_result;

bool test_main(void) {
  test_result = OK_STATUS();

  // Testing overall cryptolib low security, i.e., no jittery clock or dummy
  // instructions
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));

  for (size_t i = 0; i < ARRAYSIZE(available_security_levels); ++i) {
    current_sec_level = available_security_levels[i];
    LOG_INFO("Running CMAC tests with security level: %d", current_sec_level);

    EXECUTE_TEST(test_result, streaming_test);
    EXECUTE_TEST(test_result, one_block_test);
    EXECUTE_TEST(test_result, empty_test);
    EXECUTE_TEST(test_result, multi_block_test);

    if (status_err(test_result)) {
      break;
    }
  }

  return status_ok(test_result);
}
