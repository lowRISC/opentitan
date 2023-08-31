// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/hmac.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/hash.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

/**
 * Two-block test data.
 *
 * Test from:
 * https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA256.pdf
 *
 * SHA256('abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq')
 *  = 0x248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1
 */
static const unsigned char kTwoBlockMessage[] =
    "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
static const size_t kTwoBlockMessageLen = sizeof(kTwoBlockMessage) - 1;
static const uint8_t kTwoBlockExpDigest[] = {
    0x24, 0x8d, 0x6a, 0x61, 0xd2, 0x06, 0x38, 0xb8, 0xe5, 0xc0, 0x26,
    0x93, 0x0c, 0x3e, 0x60, 0x39, 0xa3, 0x3c, 0xe4, 0x59, 0x64, 0xff,
    0x21, 0x67, 0xf6, 0xec, 0xed, 0xd4, 0x19, 0xdb, 0x06, 0xc1};

/**
 * Test that is exactly one block in length.
 *
 * SHA256(0x102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f)
 *  = 0xfdeab9acf3710362bd2658cdc9a29e8f9c757fcf9811603a8c447cd1d9151108
 */
static const uint8_t kExactBlockMessage[] = {
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a,
    0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15,
    0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f, 0x20,
    0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28, 0x29, 0x2a, 0x2b,
    0x2c, 0x2d, 0x2e, 0x2f, 0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36,
    0x37, 0x38, 0x39, 0x3a, 0x3b, 0x3c, 0x3d, 0x3e, 0x3f,
};
static const size_t kExactBlockMessageLen = sizeof(kExactBlockMessage);
static const uint8_t kExactBlockExpDigest[] = {
    0xfd, 0xea, 0xb9, 0xac, 0xf3, 0x71, 0x03, 0x62, 0xbd, 0x26, 0x58,
    0xcd, 0xc9, 0xa2, 0x9e, 0x8f, 0x9c, 0x75, 0x7f, 0xcf, 0x98, 0x11,
    0x60, 0x3a, 0x8c, 0x44, 0x7c, 0xd1, 0xd9, 0x15, 0x11, 0x08,
};

/**
 * Call the `otcrypto_hash` API and check the resulting digest.
 *
 * @param msg Input message.
 * @param exp_digest Expected digest (256 bits).
 */
static status_t run_test(crypto_const_byte_buf_t msg,
                         const uint32_t *exp_digest) {
  uint32_t act_digest[kHmacDigestNumWords];
  crypto_word_buf_t digest_buf = {
      .data = act_digest,
      .len = kHmacDigestNumWords,
  };
  TRY(otcrypto_hash(msg, kHashModeSha256, &digest_buf));
  TRY_CHECK_ARRAYS_EQ(act_digest, exp_digest, kHmacDigestNumWords);
  return OK_STATUS();
}

/**
 * Simple test with a short message.
 *
 * SHA256('Test message.')
 *   = 0xb2da997a966ee07c43e1f083807ce5884bc0a4cad13b02cadc72a11820b50917
 */
static status_t simple_test(void) {
  const char plaintext[] = "Test message.";
  crypto_const_byte_buf_t msg_buf = {
      .data = (unsigned char *)plaintext,
      .len = sizeof(plaintext) - 1,
  };
  const uint32_t exp_digest[kHmacDigestNumWords] = {
      0x20b50917, 0xdc72a118, 0xd13b02ca, 0x4bc0a4ca,
      0x807ce588, 0x43e1f083, 0x966ee07c, 0xb2da997a,
  };
  return run_test(msg_buf, exp_digest);
}

/**
 * Test with an empty message.
 *
 * SHA256('')
 *   = 0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
 */
static status_t empty_test(void) {
  const uint32_t exp_digest[kHmacDigestNumWords] = {
      0x7852b855, 0xa495991b, 0x649b934c, 0x27ae41e4,
      0x996fb924, 0x9afbf4c8, 0x98fc1c14, 0xe3b0c442,
  };
  crypto_const_byte_buf_t msg_buf = {
      .data = NULL,
      .len = 0,
  };
  return run_test(msg_buf, exp_digest);
}

/**
 * Test streaming API with a one-block message in one update.
 */
static status_t one_update_streaming_test(void) {
  hash_context_t ctx;
  TRY(otcrypto_hash_init(&ctx, kHashModeSha256));

  crypto_const_byte_buf_t msg_buf = {
      .data = kExactBlockMessage,
      .len = kExactBlockMessageLen,
  };
  TRY(otcrypto_hash_update(&ctx, msg_buf));

  size_t digest_num_words =
      (sizeof(kExactBlockExpDigest) + sizeof(uint32_t) - 1) / sizeof(uint32_t);
  uint32_t act_digest[digest_num_words];
  crypto_word_buf_t digest_buf = {
      .data = act_digest,
      .len = digest_num_words,
  };
  TRY(otcrypto_hash_final(&ctx, &digest_buf));
  TRY_CHECK_ARRAYS_EQ((unsigned char *)act_digest, kExactBlockExpDigest,
                      sizeof(kExactBlockExpDigest));
  return OK_STATUS();
}

/**
 * Test streaming API with a two-block message in multiple updates.
 */
static status_t multiple_update_streaming_test(void) {
  hash_context_t ctx;
  TRY(otcrypto_hash_init(&ctx, kHashModeSha256));

  // Send 0 bytes, then 1, then 2, etc. until message is done.
  const unsigned char *next = kTwoBlockMessage;
  size_t len = kTwoBlockMessageLen;
  size_t update_size = 0;
  while (len > 0) {
    update_size = len <= update_size ? len : update_size;
    crypto_const_byte_buf_t msg_buf = {
        .data = next,
        .len = update_size,
    };
    next += update_size;
    len -= update_size;
    update_size++;
    TRY(otcrypto_hash_update(&ctx, msg_buf));
  }
  size_t digest_num_words =
      (sizeof(kTwoBlockExpDigest) + sizeof(uint32_t) - 1) / sizeof(uint32_t);
  uint32_t act_digest[digest_num_words];
  crypto_word_buf_t digest_buf = {
      .data = act_digest,
      .len = digest_num_words,
  };
  TRY(otcrypto_hash_final(&ctx, &digest_buf));
  TRY_CHECK_ARRAYS_EQ((unsigned char *)act_digest, kTwoBlockExpDigest,
                      sizeof(kTwoBlockExpDigest));
  return OK_STATUS();
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t test_result = OK_STATUS();
  EXECUTE_TEST(test_result, simple_test);
  EXECUTE_TEST(test_result, empty_test);
  EXECUTE_TEST(test_result, one_update_streaming_test);
  EXECUTE_TEST(test_result, multiple_update_streaming_test);
  return status_ok(test_result);
}
