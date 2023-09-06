// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/hash.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

/**
 * First test from:
 * https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA384.pdf
 */
static const unsigned char kOneBlockMessage[] = "abc";
static const size_t kOneBlockMessageLen = 3;
static const uint8_t kOneBlockExpDigest[] = {
    0xcb, 0x00, 0x75, 0x3f, 0x45, 0xa3, 0x5e, 0x8b, 0xb5, 0xa0, 0x3d, 0x69,
    0x9a, 0xc6, 0x50, 0x07, 0x27, 0x2c, 0x32, 0xab, 0x0e, 0xde, 0xd1, 0x63,
    0x1a, 0x8b, 0x60, 0x5a, 0x43, 0xff, 0x5b, 0xed, 0x80, 0x86, 0x07, 0x2b,
    0xa1, 0xe7, 0xcc, 0x23, 0x58, 0xba, 0xec, 0xa1, 0x34, 0xc8, 0x25, 0xa7};

/**
 * Second test from:
 * https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA384.pdf
 */
static const unsigned char kTwoBlockMessage[] =
    "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjk"
    "lmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";
static const size_t kTwoBlockMessageLen = sizeof(kTwoBlockMessage) - 1;
static const uint8_t kTwoBlockExpDigest[] = {
    0x09, 0x33, 0x0c, 0x33, 0xf7, 0x11, 0x47, 0xe8, 0x3d, 0x19, 0x2f, 0xc7,
    0x82, 0xcd, 0x1b, 0x47, 0x53, 0x11, 0x1b, 0x17, 0x3b, 0x3b, 0x05, 0xd2,
    0x2f, 0xa0, 0x80, 0x86, 0xe3, 0xb0, 0xf7, 0x12, 0xfc, 0xc7, 0xc7, 0x1a,
    0x55, 0x7e, 0x2d, 0xb9, 0x66, 0xc3, 0xe9, 0xfa, 0x91, 0x74, 0x60, 0x39};

/**
 * Run a single one-shot SHA-384 test.
 */
status_t sha384_test(const unsigned char *msg, const size_t msg_len,
                     const uint8_t *expected_digest) {
  // Construct a buffer for the message.
  crypto_const_byte_buf_t input_message = {
      .data = msg,
      .len = msg_len,
  };

  // Allocate space for the computed digest.
  uint32_t actual_digest_data[384 / 32];
  crypto_word32_buf_t actual_digest = {
      .data = actual_digest_data,
      .len = ARRAYSIZE(actual_digest_data),
  };
  TRY(otcrypto_hash(input_message, kHashModeSha384, &actual_digest));

  // Check that the expected and actual digests match.
  TRY_CHECK_ARRAYS_EQ((unsigned char *)actual_digest_data, expected_digest,
                      sizeof(actual_digest_data));

  return OTCRYPTO_OK;
}

/**
 * Run a test using the SHA-384 streaming API.
 */
status_t sha384_streaming_test(const unsigned char *msg, size_t msg_len,
                               const uint8_t *expected_digest) {
  hash_context_t ctx;
  TRY(otcrypto_hash_init(&ctx, kHashModeSha384));

  // Send the message 5 bytes at a time.
  while (msg_len > 0) {
    // Construct a buffer for the next update.
    size_t len = (msg_len <= 5) ? msg_len : 5;
    crypto_const_byte_buf_t input_message = {
        .data = msg,
        .len = len,
    };
    msg += len;
    msg_len -= len;
    TRY(otcrypto_hash_update(&ctx, input_message));
  }

  // Allocate space for the computed digest.
  uint32_t actual_digest_data[384 / 32];
  crypto_word32_buf_t actual_digest = {
      .data = actual_digest_data,
      .len = ARRAYSIZE(actual_digest_data),
  };
  TRY(otcrypto_hash_final(&ctx, &actual_digest));

  // Check that the expected and actual digests match.
  TRY_CHECK_ARRAYS_EQ((unsigned char *)actual_digest_data, expected_digest,
                      sizeof(actual_digest_data));

  return OTCRYPTO_OK;
}

static status_t one_block_test(void) {
  return sha384_test(kOneBlockMessage, kOneBlockMessageLen, kOneBlockExpDigest);
}

static status_t two_block_test(void) {
  return sha384_test(kTwoBlockMessage, kTwoBlockMessageLen, kTwoBlockExpDigest);
}

static status_t streaming_test(void) {
  return sha384_streaming_test(kTwoBlockMessage, kTwoBlockMessageLen,
                               kTwoBlockExpDigest);
}

OTTF_DEFINE_TEST_CONFIG();

// Holds the test result.
static volatile status_t test_result;

bool test_main(void) {
  test_result = OK_STATUS();
  EXECUTE_TEST(test_result, one_block_test);
  EXECUTE_TEST(test_result, two_block_test);
  EXECUTE_TEST(test_result, streaming_test);
  return status_ok(test_result);
}
