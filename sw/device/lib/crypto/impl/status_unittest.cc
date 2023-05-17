// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/status.h"

#include <array>

#include "gmock/gmock.h"
#include "gtest/gtest.h"

// NOTE: This test does not verify hardening measures; it only checks that the
// "normal" contract of the functions is upheld.

namespace status_unittest {
namespace {

TEST(Status, OkIsHardenedTrue) {
  EXPECT_EQ(kCryptoStatusOK, kHardenedBoolTrue);
}

int HammingDistance(uint32_t a, uint32_t b) {
  // The hamming distance is the number of bits different between the two words.
  return bitfield_popcount32(a ^ b);
}

// Check the Hamming distances of the top-level error codes.
constexpr int kMinimumHammingDistance = 5;
TEST(Status, TopLevelStatusHammingDistance) {
  std::array<crypto_status_t, 5> error_codes = {
      kCryptoStatusBadArgs, kCryptoStatusInternalError, kCryptoStatusFatalError,
      kCryptoStatusAsyncIncomplete, kCryptoStatusNotImplemented};

  // Expect the "OK" code to have a significant Hamming distance from 0.
  EXPECT_GE(HammingDistance(kCryptoStatusOK, 0), kMinimumHammingDistance)
      << "The 'OK' status code " << kCryptoStatusOK << " is too close to zero.";

  for (const crypto_status_t status1 : error_codes) {
    // Expect a significant Hamming distance from 0.
    EXPECT_GE(HammingDistance(status1, 0), kMinimumHammingDistance)
        << "Error code " << status1 << " is too close to zero.";
    // Expect an extra significant Hamming distance from the "OK" code.
    EXPECT_GE(HammingDistance(status1, kCryptoStatusOK),
              kMinimumHammingDistance)
        << "Error code " << status1 << " is too close to the 'OK' value ("
        << kCryptoStatusOK << ").";

    // Expect a significant Hamming distance from all other error codes.
    for (const crypto_status_t status2 : error_codes) {
      if (status1 != status2) {
        EXPECT_GE(HammingDistance(status1, status2), kMinimumHammingDistance)
            << "Error codes " << status1 << " and " << status2
            << " are too close to each other.";
      }
    }
  }
}

TEST(Status, OkIsNonHardenedOk) { EXPECT_EQ(status_ok(OTCRYPTO_OK), true); }

TEST(Status, ErrorMacrosNotOk) {
  // Error macros should evaluate to non-OK statuses.
  EXPECT_EQ(status_ok(OTCRYPTO_BAD_ARGS), false);
  EXPECT_EQ(status_ok(OTCRYPTO_RECOV_ERR), false);
  EXPECT_EQ(status_ok(OTCRYPTO_FATAL_ERR), false);
  EXPECT_EQ(status_ok(OTCRYPTO_ASYNC_INCOMPLETE), false);
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

__attribute__((noinline)) status_t do_hardened_try(status_t status) {
  HARDENED_TRY(status);
  return OTCRYPTO_OK;
}

TEST(Status, HardenedTryOfNonHardenedOkIsError) {
  EXPECT_EQ(status_err(do_hardened_try(OK_STATUS())), kFailedPrecondition);
}

TEST(Status, HardenedTryOfHardenedOkIsOk) {
  EXPECT_EQ(status_ok(do_hardened_try(OTCRYPTO_OK)), true);
}

TEST(Status, HardenedTryOfErrorIsError) {
  EXPECT_EQ(status_ok(do_hardened_try(INVALID_ARGUMENT())), false);
}

TEST(Status, HardenedTryOfErrorWithTruthyArgIsError) {
  EXPECT_EQ(status_ok(do_hardened_try(INVALID_ARGUMENT(kHardenedBoolTrue))),
            false);
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
