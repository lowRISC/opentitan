// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <string.h>

#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/sha1.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

enum {
  kSha1DigestBytes = 20,
  kSha1DigestWords = kSha1DigestBytes / sizeof(uint32_t),
};

/**
 * Call `otcrypto_sha1` one-shot API and check the resulting digest against
 * expected big-endian digest bytes.
 */
static status_t run_oneshot_test(otcrypto_const_byte_buf_t msg,
                                 const uint8_t exp_digest[kSha1DigestBytes]) {
  uint32_t act_digest[kSha1DigestWords] = {0};
  otcrypto_hash_digest_t digest_buf = {
      .mode = kOtcryptoHashModeSha1,
      .data = act_digest,
      .len = kSha1DigestWords,
  };
  TRY(otcrypto_sha1(&msg, &digest_buf));
  TRY_CHECK_ARRAYS_EQ((const uint8_t *)act_digest, exp_digest,
                      kSha1DigestBytes);
  TRY_CHECK(digest_buf.mode == kOtcryptoHashModeSha1);
  return OK_STATUS();
}

/**
 * Empty message test:
 * SHA1("") = da39a3ee5e6b4b0d3255bfef95601890afd80709
 */
static status_t empty_test(void) {
  static const uint8_t kExpDigest[kSha1DigestBytes] = {
      0xda, 0x39, 0xa3, 0xee, 0x5e, 0x6b, 0x4b, 0x0d, 0x32, 0x55,
      0xbf, 0xef, 0x95, 0x60, 0x18, 0x90, 0xaf, 0xd8, 0x07, 0x09,
  };
  otcrypto_const_byte_buf_t msg_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 0);
  return run_oneshot_test(msg_buf, kExpDigest);
}

/**
 * FIPS 180-4 single-block test:
 * SHA1("abc") = a9993e364706816aba3e25717850c26c9cd0d89d
 */
static status_t abc_test(void) {
  static const unsigned char kMsg[] = "abc";
  static const uint8_t kExpDigest[kSha1DigestBytes] = {
      0xa9, 0x99, 0x3e, 0x36, 0x47, 0x06, 0x81, 0x6a, 0xba, 0x3e,
      0x25, 0x71, 0x78, 0x50, 0xc2, 0x6c, 0x9c, 0xd0, 0xd8, 0x9d,
  };
  otcrypto_const_byte_buf_t msg_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, kMsg, sizeof(kMsg) - 1);
  return run_oneshot_test(msg_buf, kExpDigest);
}

/**
 * 55-byte boundary test (maximum length that fits in a single 64-byte SHA-1
 * block with the 0x80 byte and 8-byte bit length):
 * SHA1("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnop")
 *   = 47b172810795699fe739197d1a1f5960700242f1
 */
static status_t boundary_55_bytes_test(void) {
  static const unsigned char kMsg[] =
      "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnop";
  static const uint8_t kExpDigest[kSha1DigestBytes] = {
      0x47, 0xb1, 0x72, 0x81, 0x07, 0x95, 0x69, 0x9f, 0xe7, 0x39,
      0x19, 0x7d, 0x1a, 0x1f, 0x59, 0x60, 0x70, 0x02, 0x42, 0xf1,
  };
  otcrypto_const_byte_buf_t msg_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, kMsg, sizeof(kMsg) - 1);
  return run_oneshot_test(msg_buf, kExpDigest);
}

/**
 * FIPS 180-4 56-byte two-block boundary test (0x80 fits in block 1, but the
 * 8-byte bit length spills into block 2):
 * SHA1("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")
 *   = 84983e441c3bd26ebaae4aa1f95129e5e54670f1
 */
static const unsigned char kTwoBlockMsg[] =
    "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
static const size_t kTwoBlockMsgLen = sizeof(kTwoBlockMsg) - 1;
static const uint8_t kTwoBlockExpDigest[kSha1DigestBytes] = {
    0x84, 0x98, 0x3e, 0x44, 0x1c, 0x3b, 0xd2, 0x6e, 0xba, 0xae,
    0x4a, 0xa1, 0xf9, 0x51, 0x29, 0xe5, 0xe5, 0x46, 0x70, 0xf1,
};

static status_t two_block_test(void) {
  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, kTwoBlockMsg, kTwoBlockMsgLen);
  return run_oneshot_test(msg_buf, kTwoBlockExpDigest);
}

/**
 * Exact 64-byte single-block message test:
 * SHA1(0x000102...3f) = c6138d514ffa2135bfce0ed0b8fac65669917ec7
 */
static const uint8_t kExactBlockMsg[64] = {
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a,
    0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15,
    0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f, 0x20,
    0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28, 0x29, 0x2a, 0x2b,
    0x2c, 0x2d, 0x2e, 0x2f, 0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36,
    0x37, 0x38, 0x39, 0x3a, 0x3b, 0x3c, 0x3d, 0x3e, 0x3f,
};
static const uint8_t kExactBlockExpDigest[kSha1DigestBytes] = {
    0xc6, 0x13, 0x8d, 0x51, 0x4f, 0xfa, 0x21, 0x35, 0xbf, 0xce,
    0x0e, 0xd0, 0xb8, 0xfa, 0xc6, 0x56, 0x69, 0x91, 0x7e, 0xc7,
};

static status_t exact_block_test(void) {
  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, kExactBlockMsg, sizeof(kExactBlockMsg));
  return run_oneshot_test(msg_buf, kExactBlockExpDigest);
}

/**
 * NIST 112-byte multi-block message test:
 * SHA1("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmno"
 *      "ijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu")
 *   = a49b2446a02c645bf419f995b67091253a04a259
 */
static const unsigned char kMultiBlockMsg[] =
    "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmno"
    "ijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";
static const size_t kMultiBlockMsgLen = sizeof(kMultiBlockMsg) - 1;
static const uint8_t kMultiBlockExpDigest[kSha1DigestBytes] = {
    0xa4, 0x9b, 0x24, 0x46, 0xa0, 0x2c, 0x64, 0x5b, 0xf4, 0x19,
    0xf9, 0x95, 0xb6, 0x70, 0x91, 0x25, 0x3a, 0x04, 0xa2, 0x59,
};

static status_t multi_block_test(void) {
  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, kMultiBlockMsg, kMultiBlockMsgLen);
  return run_oneshot_test(msg_buf, kMultiBlockExpDigest);
}

/**
 * Streaming SHA-1 test with multiple chunk sizes (all-at-once, 5-byte chunks,
 * 1-byte chunks, and 0-length updates).
 */
static status_t streaming_test(void) {
  otcrypto_sha1_context_t ctx;
  uint32_t act_digest[kSha1DigestWords] = {0};
  otcrypto_hash_digest_t digest_buf = {
      .mode = kOtcryptoHashModeSha3_224,
      .data = act_digest,
      .len = kSha1DigestWords,
  };

  // 1. Streaming in a single update.
  TRY(otcrypto_sha1_init(&ctx));
  otcrypto_const_byte_buf_t full_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, kMultiBlockMsg, kMultiBlockMsgLen);
  TRY(otcrypto_sha1_update(&ctx, &full_buf));
  TRY(otcrypto_sha1_final(&ctx, &digest_buf));
  TRY_CHECK_ARRAYS_EQ((const uint8_t *)act_digest, kMultiBlockExpDigest,
                      kSha1DigestBytes);
  TRY_CHECK(digest_buf.mode == kOtcryptoHashModeSha1);

  // 2. Streaming in 5-byte chunks with interleaved 0-length updates.
  memset(act_digest, 0, sizeof(act_digest));
  TRY(otcrypto_sha1_init(&ctx));
  otcrypto_const_byte_buf_t empty_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 0);
  TRY(otcrypto_sha1_update(&ctx, &empty_buf));

  size_t offset = 0;
  const size_t kChunkSize = 5;
  while (offset < kMultiBlockMsgLen) {
    size_t n = (kMultiBlockMsgLen - offset < kChunkSize)
                   ? (kMultiBlockMsgLen - offset)
                   : kChunkSize;
    otcrypto_const_byte_buf_t chunk_buf = OTCRYPTO_MAKE_BUF(
        otcrypto_const_byte_buf_t, &kMultiBlockMsg[offset], n);
    TRY(otcrypto_sha1_update(&ctx, &chunk_buf));
    offset += n;
  }
  TRY(otcrypto_sha1_update(&ctx, &empty_buf));
  TRY(otcrypto_sha1_final(&ctx, &digest_buf));
  TRY_CHECK_ARRAYS_EQ((const uint8_t *)act_digest, kMultiBlockExpDigest,
                      kSha1DigestBytes);

  // 3. Streaming in 1-byte chunks across the 64-byte block boundary.
  memset(act_digest, 0, sizeof(act_digest));
  TRY(otcrypto_sha1_init(&ctx));
  for (size_t i = 0; i < sizeof(kExactBlockMsg); ++i) {
    otcrypto_const_byte_buf_t byte_buf =
        OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, &kExactBlockMsg[i], 1);
    TRY(otcrypto_sha1_update(&ctx, &byte_buf));
  }
  TRY(otcrypto_sha1_final(&ctx, &digest_buf));
  TRY_CHECK_ARRAYS_EQ((const uint8_t *)act_digest, kExactBlockExpDigest,
                      kSha1DigestBytes);

  // 4. Streaming 55 bytes + 1 byte + 8 bytes (64 bytes total).
  memset(act_digest, 0, sizeof(act_digest));
  TRY(otcrypto_sha1_init(&ctx));
  otcrypto_const_byte_buf_t part1 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, &kExactBlockMsg[0], 55);
  otcrypto_const_byte_buf_t part2 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, &kExactBlockMsg[55], 1);
  otcrypto_const_byte_buf_t part3 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, &kExactBlockMsg[56], 8);
  TRY(otcrypto_sha1_update(&ctx, &part1));
  TRY(otcrypto_sha1_update(&ctx, &part2));
  TRY(otcrypto_sha1_update(&ctx, &part3));
  TRY(otcrypto_sha1_final(&ctx, &digest_buf));
  TRY_CHECK_ARRAYS_EQ((const uint8_t *)act_digest, kExactBlockExpDigest,
                      kSha1DigestBytes);

  return OK_STATUS();
}

/**
 * Negative tests for invalid parameters and uninitialized/finalized contexts.
 */
static status_t negative_test(void) {
  uint32_t digest_data[kSha1DigestWords] = {0};
  otcrypto_hash_digest_t digest_buf = {
      .mode = kOtcryptoHashModeSha1,
      .data = digest_data,
      .len = kSha1DigestWords,
  };
  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, kTwoBlockMsg, kTwoBlockMsgLen);

  // NULL arguments to one-shot SHA-1.
  TRY_CHECK(otcrypto_sha1(NULL, &digest_buf).value ==
            kOtcryptoStatusValueBadArgs);
  TRY_CHECK(otcrypto_sha1(&msg_buf, NULL).value == kOtcryptoStatusValueBadArgs);

  // Wrong digest word length.
  otcrypto_hash_digest_t bad_len_digest = {
      .mode = kOtcryptoHashModeSha1,
      .data = digest_data,
      .len = kSha1DigestWords + 1,
  };
  TRY_CHECK(otcrypto_sha1(&msg_buf, &bad_len_digest).value ==
            kOtcryptoStatusValueBadArgs);

  // Using an uninitialized context or reusing a finalized context must fail.
  otcrypto_sha1_context_t ctx = {{0}};
  TRY_CHECK(otcrypto_sha1_update(&ctx, &msg_buf).value ==
            kOtcryptoStatusValueBadArgs);
  TRY_CHECK(otcrypto_sha1_final(&ctx, &digest_buf).value ==
            kOtcryptoStatusValueBadArgs);

  TRY(otcrypto_sha1_init(&ctx));
  TRY(otcrypto_sha1_final(&ctx, &digest_buf));
  TRY_CHECK(otcrypto_sha1_final(&ctx, &digest_buf).value ==
            kOtcryptoStatusValueBadArgs);

  return OK_STATUS();
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t test_result = OK_STATUS();

  otcrypto_state_t state = {0};
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow, &state));

  EXECUTE_TEST(test_result, empty_test);
  EXECUTE_TEST(test_result, abc_test);
  EXECUTE_TEST(test_result, boundary_55_bytes_test);
  EXECUTE_TEST(test_result, two_block_test);
  EXECUTE_TEST(test_result, exact_block_test);
  EXECUTE_TEST(test_result, multi_block_test);
  EXECUTE_TEST(test_result, streaming_test);
  EXECUTE_TEST(test_result, negative_test);

  return status_ok(test_result);
}
