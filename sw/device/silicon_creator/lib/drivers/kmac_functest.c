// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/kmac.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "kmac_regs.h"

OTTF_DEFINE_TEST_CONFIG();

/**
 * Test data: short message with short output.
 */
static const char short_msg[] = "Test message!";
static const size_t short_msg_len = 13;
static const uint32_t short_msg_digest[8] = {
    0x84f1c984, 0x7a0316bb, 0xe404cfed, 0x83f9078a,
    0x21491adc, 0xd6c30988, 0xc6822ff6, 0x20b73405,
};

/**
 * Test data: long message with long output.
 */
static const char long_msg[] =
    "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuv"
    "wxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";
static const size_t long_msg_len = 26 * 4;
static const uint32_t long_msg_digest[75] = {
    0x262992ca, 0xe4790cf1, 0x7681c77f, 0xa5366b52, 0x86490a2f, 0xf072d4c9,
    0xd4ea499a, 0x7a192fd2, 0xe1156b59, 0xb8f00ad5, 0x2ff4ba7c, 0xdec27032,
    0x33624f74, 0x88836d86, 0x4c3c6982, 0xb9e841e1, 0x78acb95a, 0x0bdbc7bc,
    0xfddfb2b5, 0x341b7524, 0x0f348bd8, 0x72b689c2, 0xd00a6e55, 0xbac16e94,
    0x5f736b17, 0xce6c5d57, 0x1fa14eb8, 0xced894a2, 0x438c5219, 0xe9eda7a1,
    0x772984f0, 0xea524c61, 0x99f75a75, 0x0ea04b06, 0x0e45a0f8, 0xf4848bd3,
    0x603d42ab, 0xd1994325, 0x5b93f17b, 0x7a88fc50, 0x469bae3b, 0x7ca37e79,
    0xb14209b8, 0x2a7b76f4, 0x434030f5, 0x7ecb89a1, 0x7ec91dfc, 0x2c58d145,
    0x8057038c, 0xbf5961fd, 0xe7b8ec78, 0x719bcc86, 0x60cb10cb, 0x35e2cb69,
    0xa6e9b0c3, 0x3f40cca6, 0x0df368d1, 0x9b122f5b, 0x63c9e1be, 0x58a9070d,
    0x384dafe8, 0x87c4e8f7, 0x5a8c247e, 0x8862d6fa, 0x3a1dd9e8, 0x6fbd6519,
    0x4c2f5eb7, 0x1358ac89, 0x0f9c5541, 0xfc98c30f, 0x15395844, 0x21e7e2d2,
    0x422b1325, 0xc1f9f225, 0x8951c775,
};

rom_error_t shake256_test(size_t input_len, const char *input,
                          size_t output_len, const uint32_t *exp_output) {
  LOG_INFO("Running SHAKE-256 with input len %d and output len %d...",
           input_len, output_len);

  RETURN_IF_ERROR(kmac_shake256_start());

  // Absorb in two steps.
  kmac_shake256_absorb((unsigned char *)input, input_len / 2);
  kmac_shake256_absorb((unsigned char *)&input[input_len / 2],
                       input_len - (input_len / 2));

  // Squeeze output.
  uint32_t act_output[output_len];
  kmac_shake256_squeeze_start();
  RETURN_IF_ERROR(kmac_shake256_squeeze_end(act_output, output_len));

  // Check output matches expectations.
  CHECK_ARRAYS_EQ(act_output, exp_output, output_len);

  return kErrorOk;
}

rom_error_t kmac_test(void) {
  // Configure KMAC to run SHAKE-256.
  RETURN_IF_ERROR(kmac_shake256_configure());

  // Simple test.
  RETURN_IF_ERROR(shake256_test(short_msg_len, short_msg,
                                ARRAYSIZE(short_msg_digest), short_msg_digest));

  // Test with long input, short output.
  RETURN_IF_ERROR(shake256_test(long_msg_len, long_msg, 1, long_msg_digest));

  // Test with long input, long output.
  RETURN_IF_ERROR(shake256_test(long_msg_len, long_msg,
                                ARRAYSIZE(long_msg_digest), long_msg_digest));

  return kErrorOk;
}

bool test_main(void) {
  // Disable all entropy. The test should also succeed with entropy enabled,
  // but KMAC blocking on entropy for SHAKE-256 would be unexpected and
  // potentially dangerous behavior for ROM. We disable it here so that if
  // that's happening the test will fail.
  CHECK_STATUS_OK(entropy_testutils_stop_all());

  status_t result = OK_STATUS();
  EXECUTE_TEST(result, kmac_test);
  return status_ok(result);
}
