// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/status.h"

#include "gmock/gmock.h"
#include "gtest/gtest.h"

// NOTE: This test does not verify hardening measures; it only checks that the
// "normal" contract of the functions is upheld.

namespace status_unittest {
namespace {

TEST(Status, OkIsHardenedOk) {
  EXPECT_EQ(hardened_status_ok(OTCRYPTO_OK), kHardenedBoolTrue);
}

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
  EXPECT_EQ(hardened_status_ok(OTCRYPTO_BAD_ARGS), kHardenedBoolFalse);
  EXPECT_EQ(hardened_status_ok(OTCRYPTO_RECOV_ERR), kHardenedBoolFalse);
  EXPECT_EQ(hardened_status_ok(OTCRYPTO_FATAL_ERR), kHardenedBoolFalse);
  EXPECT_EQ(hardened_status_ok(OTCRYPTO_ASYNC_INCOMPLETE), kHardenedBoolFalse);
}

TEST(Status, InterpretErrorMacros) {
  // Error macros should translate to the crypto status implied by their name.
  EXPECT_EQ(crypto_status_interpret(OTCRYPTO_OK), kCryptoStatusOK);
  EXPECT_EQ(crypto_status_interpret(OTCRYPTO_BAD_ARGS), kCryptoStatusBadArgs);
  EXPECT_EQ(crypto_status_interpret(OTCRYPTO_RECOV_ERR),
            kCryptoStatusInternalError);
  EXPECT_EQ(crypto_status_interpret(OTCRYPTO_FATAL_ERR),
            kCryptoStatusFatalError);
  EXPECT_EQ(crypto_status_interpret(OTCRYPTO_ASYNC_INCOMPLETE),
            kCryptoStatusAsyncIncomplete);
}

__attribute__((noinline)) crypto_status_t try_interpret(status_t status) {
  OTCRYPTO_TRY_INTERPRET(status);
  return kCryptoStatusOK;
}

TEST(Status, TryInterpretOk) {
  // Hardened OK should result in an OK status.
  EXPECT_EQ(try_interpret(OTCRYPTO_OK), kCryptoStatusOK);
}

TEST(Status, TryInterpretNonHardenedOk) {
  // Non-hardened OK should result in an error.
  EXPECT_EQ(try_interpret(OK_STATUS()), kCryptoStatusInternalError);
}

TEST(Status, TryInterpretErrors) {
  // Error macros should result in error statuses.
  EXPECT_EQ(try_interpret(OTCRYPTO_BAD_ARGS), kCryptoStatusBadArgs);
  EXPECT_EQ(try_interpret(OTCRYPTO_RECOV_ERR), kCryptoStatusInternalError);
  EXPECT_EQ(try_interpret(OTCRYPTO_FATAL_ERR), kCryptoStatusFatalError);
  EXPECT_EQ(try_interpret(OTCRYPTO_ASYNC_INCOMPLETE),
            kCryptoStatusAsyncIncomplete);
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
