// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/sha2/sha256.h"
#include "sw/device/lib/crypto/impl/sha2/sha384.h"
#include "sw/device/lib/crypto/impl/sha2/sha512.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top/entropy_src_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// ============================================================================
// SHA-256 Test Vectors
// ============================================================================
static const uint8_t kSha256EmptyExpDigest[kSha256DigestBytes] = {
    0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14, 0x9a, 0xfb, 0xf4,
    0xc8, 0x99, 0x6f, 0xb9, 0x24, 0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b,
    0x93, 0x4c, 0xa4, 0x95, 0x99, 0x1b, 0x78, 0x52, 0xb8, 0x55,
};

static const unsigned char kSha256OneBlockMsg[] = "abc";
static const size_t kSha256OneBlockMsgLen = 3;
static const uint8_t kSha256OneBlockExpDigest[kSha256DigestBytes] = {
    0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea, 0x41, 0x41, 0x40,
    0xde, 0x5d, 0xae, 0x22, 0x23, 0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17,
    0x7a, 0x9c, 0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad,
};

static const unsigned char kSha256TwoBlockMsg[] =
    "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
static const size_t kSha256TwoBlockMsgLen = sizeof(kSha256TwoBlockMsg) - 1;
static const uint8_t kSha256TwoBlockExpDigest[kSha256DigestBytes] = {
    0x24, 0x8d, 0x6a, 0x61, 0xd2, 0x06, 0x38, 0xb8, 0xe5, 0xc0, 0x26,
    0x93, 0x0c, 0x3e, 0x60, 0x39, 0xa3, 0x3c, 0xe4, 0x59, 0x64, 0xff,
    0x21, 0x67, 0xf6, 0xec, 0xed, 0xd4, 0x19, 0xdb, 0x06, 0xc1,
};

// ============================================================================
// SHA-384 Test Vectors
// ============================================================================
static const uint8_t kSha384EmptyExpDigest[kSha384DigestBytes] = {
    0x38, 0xb0, 0x60, 0xa7, 0x51, 0xac, 0x96, 0x38, 0x4c, 0xd9, 0x32, 0x7e,
    0xb1, 0xb1, 0xe3, 0x6a, 0x21, 0xfd, 0xb7, 0x11, 0x14, 0xbe, 0x07, 0x43,
    0x4c, 0x0c, 0xc7, 0xbf, 0x63, 0xf6, 0xe1, 0xda, 0x27, 0x4e, 0xde, 0xbf,
    0xe7, 0x6f, 0x65, 0xfb, 0xd5, 0x1a, 0xd2, 0xf1, 0x48, 0x98, 0xb9, 0x5b,
};

static const unsigned char kSha384OneBlockMsg[] = "abc";
static const size_t kSha384OneBlockMsgLen = 3;
static const uint8_t kSha384OneBlockExpDigest[kSha384DigestBytes] = {
    0xcb, 0x00, 0x75, 0x3f, 0x45, 0xa3, 0x5e, 0x8b, 0xb5, 0xa0, 0x3d, 0x69,
    0x9a, 0xc6, 0x50, 0x07, 0x27, 0x2c, 0x32, 0xab, 0x0e, 0xde, 0xd1, 0x63,
    0x1a, 0x8b, 0x60, 0x5a, 0x43, 0xff, 0x5b, 0xed, 0x80, 0x86, 0x07, 0x2b,
    0xa1, 0xe7, 0xcc, 0x23, 0x58, 0xba, 0xec, 0xa1, 0x34, 0xc8, 0x25, 0xa7,
};

static const unsigned char kSha384TwoBlockMsg[] =
    "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjk"
    "lmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";
static const size_t kSha384TwoBlockMsgLen = sizeof(kSha384TwoBlockMsg) - 1;
static const uint8_t kSha384TwoBlockExpDigest[kSha384DigestBytes] = {
    0x09, 0x33, 0x0c, 0x33, 0xf7, 0x11, 0x47, 0xe8, 0x3d, 0x19, 0x2f, 0xc7,
    0x82, 0xcd, 0x1b, 0x47, 0x53, 0x11, 0x1b, 0x17, 0x3b, 0x3b, 0x05, 0xd2,
    0x2f, 0xa0, 0x80, 0x86, 0xe3, 0xb0, 0xf7, 0x12, 0xfc, 0xc7, 0xc7, 0x1a,
    0x55, 0x7e, 0x2d, 0xb9, 0x66, 0xc3, 0xe9, 0xfa, 0x91, 0x74, 0x60, 0x39,
};

// ============================================================================
// SHA-512 Test Vectors
// ============================================================================
static const uint8_t kSha512EmptyExpDigest[kSha512DigestBytes] = {
    0xcf, 0x83, 0xe1, 0x35, 0x7e, 0xef, 0xb8, 0xbd, 0xf1, 0x54, 0x28,
    0x50, 0xd6, 0x6d, 0x80, 0x07, 0xd6, 0x20, 0xe4, 0x05, 0x0b, 0x57,
    0x15, 0xdc, 0x83, 0xf4, 0xa9, 0x21, 0xd3, 0x6c, 0xe9, 0xce, 0x47,
    0xd0, 0xd1, 0x3c, 0x5d, 0x85, 0xf2, 0xb0, 0xff, 0x83, 0x18, 0xd2,
    0x87, 0x7e, 0xec, 0x2f, 0x63, 0xb9, 0x31, 0xbd, 0x47, 0x41, 0x7a,
    0x81, 0xa5, 0x38, 0x32, 0x7a, 0xf9, 0x27, 0xda, 0x3e,
};

static const unsigned char kSha512OneBlockMsg[] = "abc";
static const size_t kSha512OneBlockMsgLen = 3;
static const uint8_t kSha512OneBlockExpDigest[kSha512DigestBytes] = {
    0xdd, 0xaf, 0x35, 0xa1, 0x93, 0x61, 0x7a, 0xba, 0xcc, 0x41, 0x73,
    0x49, 0xae, 0x20, 0x41, 0x31, 0x12, 0xe6, 0xfa, 0x4e, 0x89, 0xa9,
    0x7e, 0xa2, 0x0a, 0x9e, 0xee, 0xe6, 0x4b, 0x55, 0xd3, 0x9a, 0x21,
    0x92, 0x99, 0x2a, 0x27, 0x4f, 0xc1, 0xa8, 0x36, 0xba, 0x3c, 0x23,
    0xa3, 0xfe, 0xeb, 0xbd, 0x45, 0x4d, 0x44, 0x23, 0x64, 0x3c, 0xe8,
    0x0e, 0x2a, 0x9a, 0xc9, 0x4f, 0xa5, 0x4c, 0xa4, 0x9f,
};

static const unsigned char kSha512TwoBlockMsg[] =
    "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjk"
    "lmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";
static const size_t kSha512TwoBlockMsgLen = sizeof(kSha512TwoBlockMsg) - 1;
static const uint8_t kSha512TwoBlockExpDigest[kSha512DigestBytes] = {
    0x8e, 0x95, 0x9b, 0x75, 0xda, 0xe3, 0x13, 0xda, 0x8c, 0xf4, 0xf7,
    0x28, 0x14, 0xfc, 0x14, 0x3f, 0x8f, 0x77, 0x79, 0xc6, 0xeb, 0x9f,
    0x7f, 0xa1, 0x72, 0x99, 0xae, 0xad, 0xb6, 0x88, 0x90, 0x18, 0x50,
    0x1d, 0x28, 0x9e, 0x49, 0x00, 0xf7, 0xe4, 0x33, 0x1b, 0x99, 0xde,
    0xc4, 0xb5, 0x43, 0x3a, 0xc7, 0xd3, 0x29, 0xee, 0xb6, 0xdd, 0x26,
    0x54, 0x5e, 0x96, 0xe5, 0x5b, 0x87, 0x4b, 0xe9, 0x09,
};

// ============================================================================
// Multi-batch (1024-byte 'a' * 1024) Test Vectors
// Exceeds single OTBN run capacity (16 blocks for SHA-256, 6 blocks for
// SHA-384/512)
// ============================================================================
enum {
  kLongMsgLen = 1024,
};

static const uint8_t kSha256LongExpDigest[kSha256DigestBytes] = {
    0x2e, 0xdc, 0x98, 0x68, 0x47, 0xe2, 0x09, 0xb4, 0x01, 0x6e, 0x14,
    0x1a, 0x6d, 0xc8, 0x71, 0x6d, 0x32, 0x07, 0x35, 0x0f, 0x41, 0x69,
    0x69, 0x38, 0x2d, 0x43, 0x15, 0x39, 0xbf, 0x29, 0x2e, 0x4a,
};

static const uint8_t kSha384LongExpDigest[kSha384DigestBytes] = {
    0xa3, 0x1b, 0xea, 0x58, 0x96, 0xef, 0x0e, 0x41, 0x8f, 0x18, 0x01, 0x4e,
    0xf9, 0xfd, 0xe8, 0x9f, 0x6f, 0x33, 0xa1, 0x77, 0xdc, 0x97, 0x19, 0x0b,
    0xc3, 0x9d, 0xed, 0xd9, 0x4e, 0x54, 0x76, 0x34, 0x2a, 0x0d, 0x27, 0x7c,
    0x92, 0xbc, 0x19, 0xca, 0x05, 0x42, 0xfc, 0xa2, 0x27, 0xd1, 0x2c, 0x4c,
};

static const uint8_t kSha512LongExpDigest[kSha512DigestBytes] = {
    0x74, 0xb2, 0x24, 0x92, 0xe3, 0xb9, 0xa8, 0x6a, 0x9c, 0x93, 0xc2,
    0x3a, 0x69, 0xf8, 0x21, 0xeb, 0xaf, 0xa4, 0x29, 0x30, 0x2c, 0x1f,
    0x40, 0x54, 0xb4, 0xbc, 0x37, 0x35, 0x6a, 0x4b, 0xae, 0x05, 0x6d,
    0x9c, 0xcb, 0xc6, 0xf2, 0x40, 0x93, 0xa2, 0x57, 0x04, 0xfa, 0xaa,
    0x72, 0xbd, 0x21, 0xa5, 0xf3, 0x37, 0xca, 0x9e, 0xc9, 0x2f, 0x32,
    0x36, 0x9d, 0x24, 0xe6, 0xb9, 0xfa, 0xe9, 0x54, 0xd8,
};

// ============================================================================
// SHA-256 Tests
// ============================================================================
static status_t sha256_one_shot_test(const uint8_t *msg, size_t len,
                                     const uint8_t *exp_digest) {
  uint32_t act_digest[kSha256DigestWords];
  status_t res = sha256(msg, len, act_digest);
  if (!status_ok(res)) {
    uint32_t err_bits = otbn_err_bits_get();
    LOG_INFO("sha256 failed: status=0x%08x, otbn_err_bits=0x%08x", res.value,
             err_bits);
    if ((err_bits & 0x8) != 0) {
      LOG_INFO(
          "OTBN raised ILLEGAL_INSN (bit 3): physical silicon chip does not "
          "implement the custom MAI hardware extension (otbn_mai.sv).");
    }
  }
  TRY(res);
  TRY_CHECK_ARRAYS_EQ((uint8_t *)act_digest, exp_digest, kSha256DigestBytes);
  return OTCRYPTO_OK;
}

static status_t sha256_streaming_test(const uint8_t *msg, size_t len,
                                      size_t chunk_size,
                                      const uint8_t *exp_digest) {
  sha256_state_t state;
  TRY(sha256_init(&state));
  while (len > 0) {
    size_t chunk = (len <= chunk_size) ? len : chunk_size;
    TRY(sha256_update(&state, msg, chunk));
    msg += chunk;
    len -= chunk;
  }
  uint32_t act_digest[kSha256DigestWords];
  TRY(sha256_final(&state, act_digest));
  TRY_CHECK_ARRAYS_EQ((uint8_t *)act_digest, exp_digest, kSha256DigestBytes);
  return OTCRYPTO_OK;
}

static status_t test_sha256_all(void) {
  LOG_INFO("Running OTBN masked SHA-256 tests...");
  TRY(sha256_one_shot_test(NULL, 0, kSha256EmptyExpDigest));
  TRY(sha256_one_shot_test(kSha256OneBlockMsg, kSha256OneBlockMsgLen,
                           kSha256OneBlockExpDigest));
  TRY(sha256_one_shot_test(kSha256TwoBlockMsg, kSha256TwoBlockMsgLen,
                           kSha256TwoBlockExpDigest));
  TRY(sha256_streaming_test(kSha256TwoBlockMsg, kSha256TwoBlockMsgLen, 5,
                            kSha256TwoBlockExpDigest));

  uint8_t long_msg[kLongMsgLen];
  memset(long_msg, 'a', sizeof(long_msg));
  TRY(sha256_one_shot_test(long_msg, sizeof(long_msg), kSha256LongExpDigest));
  TRY(sha256_streaming_test(long_msg, sizeof(long_msg), 100,
                            kSha256LongExpDigest));

  LOG_INFO("OTBN masked SHA-256 tests succeeded.");
  return OTCRYPTO_OK;
}

// ============================================================================
// SHA-384 Tests
// ============================================================================
static status_t sha384_one_shot_test(const uint8_t *msg, size_t len,
                                     const uint8_t *exp_digest) {
  uint32_t act_digest[kSha384DigestWords];
  TRY(sha384(msg, len, act_digest));
  TRY_CHECK_ARRAYS_EQ((uint8_t *)act_digest, exp_digest, kSha384DigestBytes);
  return OTCRYPTO_OK;
}

static status_t sha384_streaming_test(const uint8_t *msg, size_t len,
                                      size_t chunk_size,
                                      const uint8_t *exp_digest) {
  sha384_state_t state;
  TRY(sha384_init(&state));
  while (len > 0) {
    size_t chunk = (len <= chunk_size) ? len : chunk_size;
    TRY(sha384_update(&state, msg, chunk));
    msg += chunk;
    len -= chunk;
  }
  uint32_t act_digest[kSha384DigestWords];
  TRY(sha384_final(&state, act_digest));
  TRY_CHECK_ARRAYS_EQ((uint8_t *)act_digest, exp_digest, kSha384DigestBytes);
  return OTCRYPTO_OK;
}

static status_t test_sha384_all(void) {
  LOG_INFO("Running OTBN masked SHA-384 tests...");
  TRY(sha384_one_shot_test(NULL, 0, kSha384EmptyExpDigest));
  TRY(sha384_one_shot_test(kSha384OneBlockMsg, kSha384OneBlockMsgLen,
                           kSha384OneBlockExpDigest));
  TRY(sha384_one_shot_test(kSha384TwoBlockMsg, kSha384TwoBlockMsgLen,
                           kSha384TwoBlockExpDigest));
  TRY(sha384_streaming_test(kSha384TwoBlockMsg, kSha384TwoBlockMsgLen, 5,
                            kSha384TwoBlockExpDigest));

  uint8_t long_msg[kLongMsgLen];
  memset(long_msg, 'a', sizeof(long_msg));
  TRY(sha384_one_shot_test(long_msg, sizeof(long_msg), kSha384LongExpDigest));
  TRY(sha384_streaming_test(long_msg, sizeof(long_msg), 100,
                            kSha384LongExpDigest));

  LOG_INFO("OTBN masked SHA-384 tests succeeded.");
  return OTCRYPTO_OK;
}

// ============================================================================
// SHA-512 Tests
// ============================================================================
static status_t sha512_one_shot_test(const uint8_t *msg, size_t len,
                                     const uint8_t *exp_digest) {
  uint32_t act_digest[kSha512DigestWords];
  TRY(sha512(msg, len, act_digest));
  TRY_CHECK_ARRAYS_EQ((uint8_t *)act_digest, exp_digest, kSha512DigestBytes);
  return OTCRYPTO_OK;
}

static status_t sha512_streaming_test(const uint8_t *msg, size_t len,
                                      size_t chunk_size,
                                      const uint8_t *exp_digest) {
  sha512_state_t state;
  TRY(sha512_init(&state));
  while (len > 0) {
    size_t chunk = (len <= chunk_size) ? len : chunk_size;
    TRY(sha512_update(&state, msg, chunk));
    msg += chunk;
    len -= chunk;
  }
  uint32_t act_digest[kSha512DigestWords];
  TRY(sha512_final(&state, act_digest));
  TRY_CHECK_ARRAYS_EQ((uint8_t *)act_digest, exp_digest, kSha512DigestBytes);
  return OTCRYPTO_OK;
}

static status_t test_sha512_all(void) {
  LOG_INFO("Running OTBN masked SHA-512 tests...");
  TRY(sha512_one_shot_test(NULL, 0, kSha512EmptyExpDigest));
  TRY(sha512_one_shot_test(kSha512OneBlockMsg, kSha512OneBlockMsgLen,
                           kSha512OneBlockExpDigest));
  TRY(sha512_one_shot_test(kSha512TwoBlockMsg, kSha512TwoBlockMsgLen,
                           kSha512TwoBlockExpDigest));
  TRY(sha512_streaming_test(kSha512TwoBlockMsg, kSha512TwoBlockMsgLen, 5,
                            kSha512TwoBlockExpDigest));

  uint8_t long_msg[kLongMsgLen];
  memset(long_msg, 'a', sizeof(long_msg));
  TRY(sha512_one_shot_test(long_msg, sizeof(long_msg), kSha512LongExpDigest));
  TRY(sha512_streaming_test(long_msg, sizeof(long_msg), 100,
                            kSha512LongExpDigest));

  LOG_INFO("OTBN masked SHA-512 tests succeeded.");
  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG(.ignore_alerts = true);

bool test_main(void) {
  status_t test_result = OK_STATUS();
  if (abs_mmio_read32(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR +
                      ENTROPY_SRC_REGWEN_REG_OFFSET) != 0) {
    CHECK_STATUS_OK(entropy_complex_init(kHardenedBoolTrue));
  }
  EXECUTE_TEST(test_result, test_sha256_all);
  EXECUTE_TEST(test_result, test_sha384_all);
  EXECUTE_TEST(test_result, test_sha512_all);
  return status_ok(test_result);
}
