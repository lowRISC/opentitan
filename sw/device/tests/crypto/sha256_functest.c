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
static const uint8_t kTwoBlockExpDigest[] = {
    0x24, 0x8d, 0x6a, 0x61, 0xd2, 0x06, 0x38, 0xb8, 0xe5, 0xc0, 0x26,
    0x93, 0x0c, 0x3e, 0x60, 0x39, 0xa3, 0x3c, 0xe4, 0x59, 0x64, 0xff,
    0x21, 0x67, 0xf6, 0xec, 0xed, 0xd4, 0x19, 0xdb, 0x06, 0xc1};

/**
 * Call the `otcrypto_hash` API and check the resulting digest.
 *
 * @param msg Input message.
 * @param exp_digest Expected digest (256 bits).
 */
static status_t run_test(crypto_const_uint8_buf_t msg,
                         const uint32_t *exp_digest) {
  uint32_t act_digest[kHmacDigestNumWords];
  crypto_uint8_buf_t digest_buf = {
      .data = (unsigned char *)act_digest,
      .len = sizeof(act_digest),
  };
  crypto_status_t status = otcrypto_hash(msg, kHashModeSha256, &digest_buf);
  TRY_CHECK(status == kCryptoStatusOK, "Error during hash operation: 0x%08x",
            status);
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
  crypto_const_uint8_buf_t msg_buf = {
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
  crypto_const_uint8_buf_t msg_buf = {
      .data = NULL,
      .len = 0,
  };
  return run_test(msg_buf, exp_digest);
}

/**
 * Test streaming API with a two-block message.
 */
static status_t streaming_test(void) {
  hash_context_t ctx;
  TRY_CHECK(otcrypto_hash_init(&ctx, kHashModeSha256) == kCryptoStatusOK);

  // Send 0 bytes, then 1, then 2, etc. until message is done.
  const unsigned char *next = kTwoBlockMessage;
  size_t len = sizeof(kTwoBlockMessage) - 1;
  size_t update_size = 0;
  while (len > 0) {
    update_size = len <= update_size ? len : update_size;
    crypto_const_uint8_buf_t msg_buf = {
        .data = next,
        .len = update_size,
    };
    next += update_size;
    len -= update_size;
    update_size++;
    TRY_CHECK(otcrypto_hash_update(&ctx, msg_buf) == kCryptoStatusOK);
  }
  uint8_t act_digest[ARRAYSIZE(kTwoBlockExpDigest)];
  crypto_uint8_buf_t digest_buf = {
      .data = act_digest,
      .len = sizeof(act_digest),
  };
  TRY_CHECK(otcrypto_hash_final(&ctx, &digest_buf) == kCryptoStatusOK);
  TRY_CHECK_ARRAYS_EQ(act_digest, kTwoBlockExpDigest,
                      ARRAYSIZE(kTwoBlockExpDigest));
  return OK_STATUS();
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t test_result = OK_STATUS();
  EXECUTE_TEST(test_result, simple_test);
  EXECUTE_TEST(test_result, empty_test);
  EXECUTE_TEST(test_result, streaming_test);
  return status_ok(test_result);
}
