// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <string.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/cryptolib_build_info.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/sha1.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

enum {
  kHmacSha1TagBytes = 20,
  kHmacSha1TagWords = kHmacSha1TagBytes / sizeof(uint32_t),
};

static const otcrypto_key_security_level_t kSecurityLevels[] = {
    kOtcryptoKeySecurityLevelLow,
    kOtcryptoKeySecurityLevelMedium,
    kOtcryptoKeySecurityLevelHigh,
};

static otcrypto_key_security_level_t current_sec_level =
    kOtcryptoKeySecurityLevelLow;

// Random mask for testing (large enough for an 80-byte key = 20 words).
static const uint32_t kTestMask[20] = {
    0x8cb847c3, 0xc6d34f36, 0x72edbf7b, 0x9bc031da, 0x8f003c7f,
    0x1d7ba049, 0x0463b6b0, 0xbb327248, 0x30f2c1f2, 0x5c720d0e,
    0x27eb6f13, 0x1c992652, 0x41a6c27c, 0x628b93a8, 0x95218a91,
    0x3370f6f8, 0x7a4e1201, 0x0911bc55, 0xef8812d4, 0xa0b1c2d3,
};

/**
 * Helper to construct an HMAC-SHA-1 blinded key from raw key bytes and run
 * `otcrypto_hmac_sha1`.
 */
static status_t run_hmac_sha1_oneshot(
    const uint8_t *key_bytes, size_t key_len, otcrypto_const_byte_buf_t msg,
    const uint8_t exp_tag[kHmacSha1TagBytes]) {
  otcrypto_key_config_t config = {
      .version = otcrypto_lib_version(),
      .key_mode = kOtcryptoKeyModeHmacSha1,
      .key_length = key_len,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = current_sec_level,
  };

  size_t key_words = ceil_div(key_len, sizeof(uint32_t));
  uint32_t raw_key_words[key_words];
  memset(raw_key_words, 0, sizeof(raw_key_words));
  memcpy(raw_key_words, key_bytes, key_len);

  uint32_t keyblob[keyblob_num_words(config)];
  TRY(keyblob_from_key_and_mask(raw_key_words, kTestMask, config, keyblob));
  otcrypto_blinded_key_t blinded_key = {
      .config = config,
      .keyblob = keyblob,
      .keyblob_length = sizeof(keyblob),
      .checksum = 0,
  };
  blinded_key.checksum = otcrypto_integrity_blinded_checksum(&blinded_key);

  uint32_t act_tag[kHmacSha1TagWords] = {0};
  otcrypto_word32_buf_t tag_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, act_tag, ARRAYSIZE(act_tag));
  TRY(otcrypto_hmac_sha1(&blinded_key, &msg, &tag_buf));
  TRY_CHECK_ARRAYS_EQ((const uint8_t *)act_tag, exp_tag, kHmacSha1TagBytes);
  return OK_STATUS();
}

/**
 * RFC 2202 Test Case 1:
 * key = 0x0b repeated 20 times (20 bytes)
 * data = "Hi There" (8 bytes)
 * digest = 0xb617318655057264e28bc0b6fb378c8ef146be00
 */
static const uint8_t kRfc2202Key1[20] = {
    0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b,
    0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b,
};
static const unsigned char kRfc2202Data1[] = "Hi There";
static const uint8_t kRfc2202ExpTag1[kHmacSha1TagBytes] = {
    0xb6, 0x17, 0x31, 0x86, 0x55, 0x05, 0x72, 0x64, 0xe2, 0x8b,
    0xc0, 0xb6, 0xfb, 0x37, 0x8c, 0x8e, 0xf1, 0x46, 0xbe, 0x00,
};

static status_t rfc2202_case1_test(void) {
  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, kRfc2202Data1, sizeof(kRfc2202Data1) - 1);
  return run_hmac_sha1_oneshot(kRfc2202Key1, sizeof(kRfc2202Key1), msg_buf,
                               kRfc2202ExpTag1);
}

/**
 * RFC 2202 Test Case 2 (short 4-byte key "Jefe"):
 * key = "Jefe" (4 bytes)
 * data = "what do ya want for nothing?" (28 bytes)
 * digest = 0xeffcdf6ae5eb2fa2d27416d5f184df9c259a7c79
 */
static const uint8_t kRfc2202Key2[] = {'J', 'e', 'f', 'e'};
static const unsigned char kRfc2202Data2[] = "what do ya want for nothing?";
static const uint8_t kRfc2202ExpTag2[kHmacSha1TagBytes] = {
    0xef, 0xfc, 0xdf, 0x6a, 0xe5, 0xeb, 0x2f, 0xa2, 0xd2, 0x74,
    0x16, 0xd5, 0xf1, 0x84, 0xdf, 0x9c, 0x25, 0x9a, 0x7c, 0x79,
};

static status_t rfc2202_case2_test(void) {
  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, kRfc2202Data2, sizeof(kRfc2202Data2) - 1);
  return run_hmac_sha1_oneshot(kRfc2202Key2, sizeof(kRfc2202Key2), msg_buf,
                               kRfc2202ExpTag2);
}

/**
 * RFC 2202 Test Case 3:
 * key = 0xaa repeated 20 times (20 bytes)
 * data = 0xdd repeated 50 times (50 bytes)
 * digest = 0x125d7342b9ac11cd91a39af48aa17b4f63f175d3
 */
static const uint8_t kRfc2202Key3[20] = {
    0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
    0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
};
static const uint8_t kRfc2202Data3[50] = {
    0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd,
    0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd,
    0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd,
    0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd,
    0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd,
};
static const uint8_t kRfc2202ExpTag3[kHmacSha1TagBytes] = {
    0x12, 0x5d, 0x73, 0x42, 0xb9, 0xac, 0x11, 0xcd, 0x91, 0xa3,
    0x9a, 0xf4, 0x8a, 0xa1, 0x7b, 0x4f, 0x63, 0xf1, 0x75, 0xd3,
};

static status_t rfc2202_case3_test(void) {
  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, kRfc2202Data3, sizeof(kRfc2202Data3));
  return run_hmac_sha1_oneshot(kRfc2202Key3, sizeof(kRfc2202Key3), msg_buf,
                               kRfc2202ExpTag3);
}

/**
 * RFC 2202 Test Case 4 (non-word-aligned 25-byte key):
 * key = 0x0102030405060708090a0b0c0d0e0f10111213141516171819 (25 bytes)
 * data = 0xcd repeated 50 times (50 bytes)
 * digest = 0x4c9007f4026250c6bc8414f9bf50c86c2d7235da
 */
static const uint8_t kRfc2202Key4[25] = {
    0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09,
    0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12,
    0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19,
};
static const uint8_t kRfc2202Data4[50] = {
    0xcd, 0xcd, 0xcd, 0xcd, 0xcd, 0xcd, 0xcd, 0xcd, 0xcd, 0xcd,
    0xcd, 0xcd, 0xcd, 0xcd, 0xcd, 0xcd, 0xcd, 0xcd, 0xcd, 0xcd,
    0xcd, 0xcd, 0xcd, 0xcd, 0xcd, 0xcd, 0xcd, 0xcd, 0xcd, 0xcd,
    0xcd, 0xcd, 0xcd, 0xcd, 0xcd, 0xcd, 0xcd, 0xcd, 0xcd, 0xcd,
    0xcd, 0xcd, 0xcd, 0xcd, 0xcd, 0xcd, 0xcd, 0xcd, 0xcd, 0xcd,
};
static const uint8_t kRfc2202ExpTag4[kHmacSha1TagBytes] = {
    0x4c, 0x90, 0x07, 0xf4, 0x02, 0x62, 0x50, 0xc6, 0xbc, 0x84,
    0x14, 0xf9, 0xbf, 0x50, 0xc8, 0x6c, 0x2d, 0x72, 0x35, 0xda,
};

static status_t rfc2202_case4_test(void) {
  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, kRfc2202Data4, sizeof(kRfc2202Data4));
  return run_hmac_sha1_oneshot(kRfc2202Key4, sizeof(kRfc2202Key4), msg_buf,
                               kRfc2202ExpTag4);
}

/**
 * RFC 2202 Test Case 6 & 7 (80-byte key > 64-byte SHA-1 block size):
 * key = 0xaa repeated 80 times (80 bytes)
 * Case 6 data = "Test Using Larger Than Block-Size Key - Hash Key First"
 * Case 6 digest = 0xaa4ae5e15272d00e95705637ce8a3b55ed402112
 * Case 7 data = "Test Using Larger Than Block-Size Key and Larger Than One "
 *               "Block-Size Data"
 * Case 7 digest = 0xe8e99d0f45237d786d6bbaa7965c7808bbff1a91
 */
static const uint8_t kRfc2202LongKey[80] = {
    0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
    0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
    0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
    0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
    0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
    0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
    0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
};
static const unsigned char kRfc2202Data6[] =
    "Test Using Larger Than Block-Size Key - Hash Key First";
static const uint8_t kRfc2202ExpTag6[kHmacSha1TagBytes] = {
    0xaa, 0x4a, 0xe5, 0xe1, 0x52, 0x72, 0xd0, 0x0e, 0x95, 0x70,
    0x56, 0x37, 0xce, 0x8a, 0x3b, 0x55, 0xed, 0x40, 0x21, 0x12,
};
static const unsigned char kRfc2202Data7[] =
    "Test Using Larger Than Block-Size Key and Larger Than One Block-Size Data";
static const uint8_t kRfc2202ExpTag7[kHmacSha1TagBytes] = {
    0xe8, 0xe9, 0x9d, 0x0f, 0x45, 0x23, 0x7d, 0x78, 0x6d, 0x6b,
    0xba, 0xa7, 0x96, 0x5c, 0x78, 0x08, 0xbb, 0xff, 0x1a, 0x91,
};

static status_t long_key_test(void) {
  otcrypto_const_byte_buf_t msg6 = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, kRfc2202Data6, sizeof(kRfc2202Data6) - 1);
  TRY(run_hmac_sha1_oneshot(kRfc2202LongKey, sizeof(kRfc2202LongKey), msg6,
                            kRfc2202ExpTag6));

  otcrypto_const_byte_buf_t msg7 = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, kRfc2202Data7, sizeof(kRfc2202Data7) - 1);
  return run_hmac_sha1_oneshot(kRfc2202LongKey, sizeof(kRfc2202LongKey), msg7,
                               kRfc2202ExpTag7);
}

/**
 * Empty message test:
 * HMAC-SHA1(kRfc2202Key1, "") = 0x123fd78bda0100786ae86b76f50f01bd18e477f3
 */
static status_t empty_message_test(void) {
  static const uint8_t kExpEmptyTag[kHmacSha1TagBytes] = {
      0x12, 0x3f, 0xd7, 0x8b, 0xda, 0x01, 0x00, 0x78, 0x6a, 0xe8,
      0x6b, 0x76, 0xf5, 0x0f, 0x01, 0xbd, 0x18, 0xe4, 0x77, 0xf3,
  };
  otcrypto_const_byte_buf_t empty_msg =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 0);
  return run_hmac_sha1_oneshot(kRfc2202Key1, sizeof(kRfc2202Key1), empty_msg,
                               kExpEmptyTag);
}

/**
 * Streaming HMAC-SHA-1 test (single update, 3-byte chunked updates, 1-byte
 * chunked updates, and 0-length updates).
 */
static status_t streaming_test(void) {
  otcrypto_key_config_t config = {
      .version = otcrypto_lib_version(),
      .key_mode = kOtcryptoKeyModeHmacSha1,
      .key_length = sizeof(kRfc2202LongKey),
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = current_sec_level,
  };

  size_t key_words = ceil_div(sizeof(kRfc2202LongKey), sizeof(uint32_t));
  uint32_t raw_key_words[key_words];
  memcpy(raw_key_words, kRfc2202LongKey, sizeof(kRfc2202LongKey));

  uint32_t keyblob[keyblob_num_words(config)];
  TRY(keyblob_from_key_and_mask(raw_key_words, kTestMask, config, keyblob));
  otcrypto_blinded_key_t blinded_key = {
      .config = config,
      .keyblob = keyblob,
      .keyblob_length = sizeof(keyblob),
      .checksum = 0,
  };
  blinded_key.checksum = otcrypto_integrity_blinded_checksum(&blinded_key);

  uint32_t act_tag[kHmacSha1TagWords] = {0};
  otcrypto_word32_buf_t tag_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, act_tag, ARRAYSIZE(act_tag));

  const size_t kMsgLen = sizeof(kRfc2202Data7) - 1;
  otcrypto_const_byte_buf_t full_msg =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, kRfc2202Data7, kMsgLen);

  // 1. Streaming in a single update.
  otcrypto_hmac_sha1_context_t ctx;
  TRY(otcrypto_hmac_sha1_init(&ctx, &blinded_key));
  TRY(otcrypto_hmac_sha1_update(&ctx, &full_msg));
  TRY(otcrypto_hmac_sha1_final(&ctx, &tag_buf));
  TRY_CHECK_ARRAYS_EQ((const uint8_t *)act_tag, kRfc2202ExpTag7,
                      kHmacSha1TagBytes);

  // 2. Streaming in 3-byte chunks with interleaved 0-length updates.
  memset(act_tag, 0, sizeof(act_tag));
  TRY(otcrypto_hmac_sha1_init(&ctx, &blinded_key));
  otcrypto_const_byte_buf_t empty_msg =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 0);
  TRY(otcrypto_hmac_sha1_update(&ctx, &empty_msg));

  size_t offset = 0;
  const size_t kChunkSize = 3;
  while (offset < kMsgLen) {
    size_t n =
        (kMsgLen - offset < kChunkSize) ? (kMsgLen - offset) : kChunkSize;
    otcrypto_const_byte_buf_t chunk_buf =
        OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, &kRfc2202Data7[offset], n);
    TRY(otcrypto_hmac_sha1_update(&ctx, &chunk_buf));
    offset += n;
  }
  TRY(otcrypto_hmac_sha1_update(&ctx, &empty_msg));
  TRY(otcrypto_hmac_sha1_final(&ctx, &tag_buf));
  TRY_CHECK_ARRAYS_EQ((const uint8_t *)act_tag, kRfc2202ExpTag7,
                      kHmacSha1TagBytes);

  return OK_STATUS();
}

/**
 * Negative tests for invalid keys, wrong key modes, bad tag lengths, and
 * uninitialized contexts.
 */
static status_t negative_test(void) {
  otcrypto_key_config_t config = {
      .version = otcrypto_lib_version(),
      .key_mode = kOtcryptoKeyModeHmacSha1,
      .key_length = sizeof(kRfc2202Key1),
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  uint32_t raw_key_words[5];
  memcpy(raw_key_words, kRfc2202Key1, sizeof(kRfc2202Key1));
  uint32_t keyblob[keyblob_num_words(config)];
  TRY(keyblob_from_key_and_mask(raw_key_words, kTestMask, config, keyblob));
  otcrypto_blinded_key_t blinded_key = {
      .config = config,
      .keyblob = keyblob,
      .keyblob_length = sizeof(keyblob),
      .checksum = 0,
  };
  blinded_key.checksum = otcrypto_integrity_blinded_checksum(&blinded_key);

  uint32_t tag_data[kHmacSha1TagWords] = {0};
  otcrypto_word32_buf_t tag_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, tag_data, ARRAYSIZE(tag_data));
  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, kRfc2202Data1, sizeof(kRfc2202Data1) - 1);

  // NULL arguments.
  TRY_CHECK(otcrypto_hmac_sha1(NULL, &msg_buf, &tag_buf).value ==
            kOtcryptoStatusValueBadArgs);
  TRY_CHECK(otcrypto_hmac_sha1(&blinded_key, NULL, &tag_buf).value ==
            kOtcryptoStatusValueBadArgs);
  TRY_CHECK(otcrypto_hmac_sha1(&blinded_key, &msg_buf, NULL).value ==
            kOtcryptoStatusValueBadArgs);

  // Wrong key mode (e.g. HMAC-SHA256 key passed to HMAC-SHA1).
  otcrypto_blinded_key_t wrong_mode_key = blinded_key;
  wrong_mode_key.config.key_mode = kOtcryptoKeyModeHmacSha256;
  wrong_mode_key.checksum =
      otcrypto_integrity_blinded_checksum(&wrong_mode_key);
  TRY_CHECK(otcrypto_hmac_sha1(&wrong_mode_key, &msg_buf, &tag_buf).value ==
            kOtcryptoStatusValueBadArgs);

  // Bad key checksum.
  otcrypto_blinded_key_t bad_checksum_key = blinded_key;
  bad_checksum_key.checksum ^= 1u;
  TRY_CHECK(otcrypto_hmac_sha1(&bad_checksum_key, &msg_buf, &tag_buf).value ==
            kOtcryptoStatusValueBadArgs);

  // Wrong tag length.
  otcrypto_word32_buf_t bad_tag_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, tag_data, kHmacSha1TagWords - 1);
  TRY_CHECK(otcrypto_hmac_sha1(&blinded_key, &msg_buf, &bad_tag_buf).value ==
            kOtcryptoStatusValueBadArgs);

  // Uninitialized / reused context.
  otcrypto_hmac_sha1_context_t ctx = {{0}};
  TRY_CHECK(otcrypto_hmac_sha1_update(&ctx, &msg_buf).value ==
            kOtcryptoStatusValueBadArgs);
  TRY_CHECK(otcrypto_hmac_sha1_final(&ctx, &tag_buf).value ==
            kOtcryptoStatusValueBadArgs);

  return OK_STATUS();
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t test_result = OK_STATUS();

  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));

  for (size_t i = 0; i < ARRAYSIZE(kSecurityLevels); ++i) {
    current_sec_level = kSecurityLevels[i];
    LOG_INFO("Running HMAC-SHA1 tests with security level: %d",
             current_sec_level);

    EXECUTE_TEST(test_result, rfc2202_case1_test);
    EXECUTE_TEST(test_result, rfc2202_case2_test);
    EXECUTE_TEST(test_result, rfc2202_case3_test);
    EXECUTE_TEST(test_result, rfc2202_case4_test);
    EXECUTE_TEST(test_result, long_key_test);
    EXECUTE_TEST(test_result, empty_message_test);
    EXECUTE_TEST(test_result, streaming_test);

    if (status_err(test_result)) {
      return false;
    }
  }

  EXECUTE_TEST(test_result, negative_test);
  return status_ok(test_result);
}
