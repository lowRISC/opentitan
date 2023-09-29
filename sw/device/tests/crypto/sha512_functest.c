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
 * https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA512.pdf
 */
static const unsigned char kOneBlockMessage[] = "abc";
static const size_t kOneBlockMessageLen = 3;
static const uint8_t kOneBlockExpDigest[] = {
    0xdd, 0xaf, 0x35, 0xa1, 0x93, 0x61, 0x7a, 0xba, 0xcc, 0x41, 0x73,
    0x49, 0xae, 0x20, 0x41, 0x31, 0x12, 0xe6, 0xfa, 0x4e, 0x89, 0xa9,
    0x7e, 0xa2, 0x0a, 0x9e, 0xee, 0xe6, 0x4b, 0x55, 0xd3, 0x9a, 0x21,
    0x92, 0x99, 0x2a, 0x27, 0x4f, 0xc1, 0xa8, 0x36, 0xba, 0x3c, 0x23,
    0xa3, 0xfe, 0xeb, 0xbd, 0x45, 0x4d, 0x44, 0x23, 0x64, 0x3c, 0xe8,
    0x0e, 0x2a, 0x9a, 0xc9, 0x4f, 0xa5, 0x4c, 0xa4, 0x9f,
};

/**
 * Second test from:
 * https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA512.pdf
 */
static const unsigned char kTwoBlockMessage[] =
    "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjk"
    "lmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";
static const size_t kTwoBlockMessageLen = sizeof(kTwoBlockMessage) - 1;
static const uint8_t kTwoBlockExpDigest[] = {
    0x8e, 0x95, 0x9b, 0x75, 0xda, 0xe3, 0x13, 0xda, 0x8c, 0xf4, 0xf7,
    0x28, 0x14, 0xfc, 0x14, 0x3f, 0x8f, 0x77, 0x79, 0xc6, 0xeb, 0x9f,
    0x7f, 0xa1, 0x72, 0x99, 0xae, 0xad, 0xb6, 0x88, 0x90, 0x18, 0x50,
    0x1d, 0x28, 0x9e, 0x49, 0x00, 0xf7, 0xe4, 0x33, 0x1b, 0x99, 0xde,
    0xc4, 0xb5, 0x43, 0x3a, 0xc7, 0xd3, 0x29, 0xee, 0xb6, 0xdd, 0x26,
    0x54, 0x5e, 0x96, 0xe5, 0x5b, 0x87, 0x4b, 0xe9, 0x09};

/**
 * Run a single one-shot SHA-512 test.
 */
status_t sha512_test(const unsigned char *msg, const size_t msg_len,
                     const uint8_t *expected_digest) {
  // Construct a buffer for the message.
  crypto_const_byte_buf_t input_message = {
      .data = msg,
      .len = msg_len,
  };

  // Allocate space for the computed digest.
  uint32_t actual_digest_data[512 / 32];
  hash_digest_t actual_digest = {
      .len = ARRAYSIZE(actual_digest_data),
      .data = actual_digest_data,
      .mode = kHashModeSha512,
  };
  TRY(otcrypto_hash(input_message, &actual_digest));

  // Check that the expected and actual digests match.
  TRY_CHECK_ARRAYS_EQ((unsigned char *)actual_digest_data, expected_digest,
                      sizeof(actual_digest_data));

  return OTCRYPTO_OK;
}

/**
 * Run a test using the SHA-512 streaming API.
 */
status_t sha512_streaming_test(const unsigned char *msg, size_t msg_len,
                               const uint8_t *expected_digest) {
  hash_context_t ctx;
  TRY(otcrypto_hash_init(&ctx, kHashModeSha512));

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
  uint32_t actual_digest_data[512 / 32];
  hash_digest_t actual_digest = {
      .data = actual_digest_data,
      .len = ARRAYSIZE(actual_digest_data),
      .mode = kHashModeSha512,
  };
  TRY(otcrypto_hash_final(&ctx, &actual_digest));

  // Check that the expected and actual digests match.
  TRY_CHECK_ARRAYS_EQ((unsigned char *)actual_digest_data, expected_digest,
                      sizeof(actual_digest_data));

  return OTCRYPTO_OK;
}

static status_t one_block_test(void) {
  return sha512_test(kOneBlockMessage, kOneBlockMessageLen, kOneBlockExpDigest);
}

static status_t two_block_test(void) {
  return sha512_test(kTwoBlockMessage, kTwoBlockMessageLen, kTwoBlockExpDigest);
}

static status_t streaming_test(void) {
  return sha512_streaming_test(kTwoBlockMessage, kTwoBlockMessageLen,
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
