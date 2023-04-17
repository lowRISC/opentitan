// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/silicon_creator/lib/crc32.h"
#include "sw/device/silicon_creator/lib/error.h"

#define LOG_TEST_PARAMS(x)                                           \
  LOG_INFO("[%s] Test params: input = 0x%!y, expected_crc32 = 0x%x", \
           __FUNCTION__, x.input_len, x.input, x.expected_crc32);

typedef struct test_params {
  const char *input;
  size_t input_len;
  uint32_t expected_crc32;
} test_params_t;

static const char kTestString1[] = "123456789";
static const char kTestString2[] =
    "The quick brown fox jumps over the lazy dog";
static const char kTestString3[] = "\xfe\xca\xfe\xca\x02\xb0\xad\x1b";

static const test_params_t kTestCases[] = {{
                                               kTestString1,
                                               sizeof(kTestString1) - 1,
                                               0xcbf43926,
                                           },
                                           {
                                               kTestString2,
                                               sizeof(kTestString2) - 1,
                                               0x414fa339,
                                           },
                                           {
                                               kTestString3,
                                               sizeof(kTestString3) - 1,
                                               0x9508ac14,
                                           }};

static rom_error_t crc32_test(void) {
  for (size_t i = 0; i < ARRAYSIZE(kTestCases); ++i) {
    LOG_TEST_PARAMS(kTestCases[i]);
    CHECK(crc32(kTestCases[i].input, kTestCases[i].input_len) ==
          kTestCases[i].expected_crc32);
  }
  return kErrorOk;
}

static rom_error_t crc32_add_test(void) {
  for (size_t i = 0; i < ARRAYSIZE(kTestCases); ++i) {
    LOG_TEST_PARAMS(kTestCases[i]);
    uint32_t ctx;
    crc32_init(&ctx);
    crc32_add(&ctx, kTestCases[i].input, kTestCases[i].input_len);
    CHECK(crc32_finish(&ctx) == kTestCases[i].expected_crc32);
  }
  return kErrorOk;
}

static rom_error_t crc32_misaligned_test(void) {
  uint32_t kExpCrc = 0x414fa339;
  alignas(uint32_t) char input[] =
      ">The quick brown fox jumps over the lazy dog";
  CHECK(crc32(&input[1], sizeof(input) - 2) == kExpCrc);

  uint32_t ctx;
  crc32_init(&ctx);
  crc32_add(&ctx, &input[1], sizeof(input) - 2);
  CHECK(crc32_finish(&ctx) == kExpCrc);
  return kErrorOk;
}

static rom_error_t crc32_add8_test(void) {
  for (size_t i = 0; i < ARRAYSIZE(kTestCases); ++i) {
    LOG_TEST_PARAMS(kTestCases[i]);
    uint32_t ctx;
    crc32_init(&ctx);
    for (size_t j = 0; j < kTestCases[i].input_len; ++j) {
      crc32_add8(&ctx, kTestCases[i].input[j]);
    }
    CHECK(crc32_finish(&ctx) == kTestCases[i].expected_crc32);
  }
  return kErrorOk;
}

static rom_error_t crc32_add32_test(void) {
  uint32_t ctx;
  crc32_init(&ctx);
  const uint32_t kExpCrc = 0x9508ac14;

  crc32_add32(&ctx, 0xcafecafe);
  crc32_finish(&ctx);
  crc32_add32(&ctx, 0x1badb002);

  CHECK(crc32_finish(&ctx) == kExpCrc);
  return kErrorOk;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t result = OK_STATUS();
  EXECUTE_TEST(result, crc32_test);
  EXECUTE_TEST(result, crc32_add_test);
  EXECUTE_TEST(result, crc32_misaligned_test);
  EXECUTE_TEST(result, crc32_add8_test);
  EXECUTE_TEST(result, crc32_add32_test);
  return status_ok(result);
}
