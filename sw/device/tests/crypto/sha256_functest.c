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
 * Call the `otcrypto_hash` API and check the resulting digest.
 *
 * @param msg Input message.
 * @param exp_digest Expected digest (256 bits).
 */
static void run_test(crypto_const_uint8_buf_t msg, const uint32_t *exp_digest) {
  uint32_t act_digest[kHmacDigestNumWords];
  crypto_uint8_buf_t digest_buf = {
      .data = (unsigned char *)act_digest,
      .len = sizeof(act_digest),
  };
  crypto_status_t status = otcrypto_hash(msg, kHashModeSha256, &digest_buf);
  CHECK(status == kCryptoStatusOK, "Error during hash operation: 0x%08x",
        status);
  CHECK_ARRAYS_EQ(act_digest, exp_digest, kHmacDigestNumWords);
}

/**
 * Simple test with a short message.
 *
 * SHA256('Test message.')
 *   = 0xb2da997a966ee07c43e1f083807ce5884bc0a4cad13b02cadc72a11820b50917
 */
static void simple_test(void) {
  const char plaintext[] = "Test message.";
  crypto_const_uint8_buf_t msg_buf = {
      .data = (unsigned char *)plaintext,
      .len = sizeof(plaintext) - 1,
  };
  const uint32_t exp_digest[kHmacDigestNumWords] = {
      0x20b50917, 0xdc72a118, 0xd13b02ca, 0x4bc0a4ca,
      0x807ce588, 0x43e1f083, 0x966ee07c, 0xb2da997a,
  };
  run_test(msg_buf, exp_digest);
}

/**
 * Test with an empty message.
 *
 * SHA256('')
 *   = 0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
 */
static void empty_test(void) {
  const uint32_t exp_digest[kHmacDigestNumWords] = {
      0x7852b855, 0xa495991b, 0x649b934c, 0x27ae41e4,
      0x996fb924, 0x9afbf4c8, 0x98fc1c14, 0xe3b0c442,
  };
  crypto_const_uint8_buf_t msg_buf = {
      .data = NULL,
      .len = 0,
  };
  run_test(msg_buf, exp_digest);
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  simple_test();
  empty_test();

  return true;
}
