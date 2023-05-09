// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <array>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "sw/device/lib/crypto/impl/status.h"

// NOTE: This test does not verify hardening measures; it only checks that the
// "normal" contract of the functions is upheld.

namespace status_unittest {
namespace {

TEST(Status, OkIsNonHardenedOk) { EXPECT_EQ(status_ok(OTCRYPTO_OK), true); }

TEST(Status, ErrorMacrosNotOk) {
  // Error macros should evaluate to non-OK statuses.
  EXPECT_EQ(status_ok(OTCRYPTO_BAD_ARGS), false);
  EXPECT_EQ(status_ok(OTCRYPTO_RECOV_ERR), false);
  EXPECT_EQ(status_ok(OTCRYPTO_FATAL_ERR), false);
  EXPECT_EQ(status_ok(OTCRYPTO_ASYNC_INCOMPLETE), false);
}

TEST(Status, ErrorMacrosNotHardenedOk) {
  // Error macros should evaluate to non-OK statuses.
  EXPECT_EQ(status_ok(OTCRYPTO_BAD_ARGS), false);
  EXPECT_EQ(status_ok(OTCRYPTO_RECOV_ERR), false);
  EXPECT_EQ(status_ok(OTCRYPTO_FATAL_ERR), false);
  EXPECT_EQ(status_ok(OTCRYPTO_ASYNC_INCOMPLETE), false);
}

TEST(Status, ErrorMacrosHaveExpectedValues) {
  // Error macros should evaluate to specific Abseil error codes.
  EXPECT_EQ(status_err(OTCRYPTO_BAD_ARGS), kInvalidArgument);
  EXPECT_EQ(status_err(OTCRYPTO_RECOV_ERR), kAborted);
  EXPECT_EQ(status_err(OTCRYPTO_FATAL_ERR), kFailedPrecondition);
  EXPECT_EQ(status_err(OTCRYPTO_ASYNC_INCOMPLETE), kUnavailable);
  EXPECT_EQ(status_err(OTCRYPTO_NOT_IMPLEMENTED), kUnimplemented);
}

__attribute__((noinline)) crypto_status_t try_interpret(status_t status) {
  HARDENED_TRY(status);
  return OTCRYPTO_OK;
}

TEST(Status, TryInterpretOk) {
  // Hardened OK should result in an OK status.
  EXPECT_EQ(status_ok(try_interpret(OTCRYPTO_OK)), true);
}

TEST(Status, TryInterpretNonHardenedOk) {
  // Non-hardened OK should result in an error.
  EXPECT_EQ(status_ok(try_interpret(OK_STATUS())), false);
}

constexpr char kTestModId[3] = {'X', 'Y', 'Z'};
#define MODULE_ID MAKE_MODULE_ID(kTestModId[0], kTestModId[1], kTestModId[2])

TEST(Status, ExtractStatusFieldsBadArgs) {
  const char *code = NULL;
  char mod_id[3] = {0};
  int32_t line = 0;
  const char expected_code[] = "InvalidArgument";
  int32_t expected_line = __LINE__ + 1;
  EXPECT_EQ(status_extract(OTCRYPTO_BAD_ARGS, &code, &line, mod_id), true);

  // Check the fields to ensure that the format of cryptolib errors matches the
  // error format from the main status library.
  EXPECT_EQ(memcmp(code, expected_code, ARRAYSIZE(expected_code)), 0);
  EXPECT_THAT(mod_id, testing::ElementsAreArray(kTestModId));
  EXPECT_EQ(line, expected_line);
}

TEST(Status, ExtractStatusFieldsRecovErr) {
  const char *code = NULL;
  char mod_id[3] = {0};
  int32_t line = 0;
  const char expected_code[] = "Aborted";
  int32_t expected_line = __LINE__ + 1;
  EXPECT_EQ(status_extract(OTCRYPTO_RECOV_ERR, &code, &line, mod_id), true);

  // Check the fields to ensure that the format of cryptolib errors matches the
  // error format from the main status library.
  EXPECT_EQ(memcmp(code, expected_code, ARRAYSIZE(expected_code)), 0);
  EXPECT_THAT(mod_id, testing::ElementsAreArray(kTestModId));
  EXPECT_EQ(line, expected_line);
}

TEST(Status, ExtractStatusFieldsFatalErr) {
  const char *code = NULL;
  char mod_id[3] = {0};
  int32_t line = 0;
  const char expected_code[] = "FailedPrecondition";
  int32_t expected_line = __LINE__ + 1;
  EXPECT_EQ(status_extract(OTCRYPTO_FATAL_ERR, &code, &line, mod_id), true);

  // Check the fields to ensure that the format of cryptolib errors matches the
  // error format from the main status library.
  EXPECT_EQ(memcmp(code, expected_code, ARRAYSIZE(expected_code)), 0);
  EXPECT_THAT(mod_id, testing::ElementsAreArray(kTestModId));
  EXPECT_EQ(line, expected_line);
}

TEST(Status, ExtractStatusFieldsAsyncIncomplete) {
  const char *code = NULL;
  char mod_id[3] = {0};
  int32_t line = 0;
  const char expected_code[] = "Unavailable";
  int32_t expected_line = __LINE__ + 1;
  EXPECT_EQ(status_extract(OTCRYPTO_ASYNC_INCOMPLETE, &code, &line, mod_id),
            true);

  // Check the fields to ensure that the format of cryptolib errors matches the
  // error format from the main status library.
  EXPECT_EQ(memcmp(code, expected_code, ARRAYSIZE(expected_code)), 0);
  EXPECT_THAT(mod_id, testing::ElementsAreArray(kTestModId));
  EXPECT_EQ(line, expected_line);
}

}  // namespace
}  // namespace status_unittest
