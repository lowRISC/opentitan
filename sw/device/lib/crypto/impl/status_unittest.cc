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

int HammingDistance(int32_t a, int32_t b) {
  // The hamming distance is the number of bits different between the two words.
  return bitfield_popcount32(a ^ b);
}

// Check the Hamming distances of the top-level error codes.
constexpr int kMinimumHammingDistance = 5;
TEST(Status, TopLevelStatusHammingDistance) {
  std::array<crypto_status_t, 5> error_codes = {
      OTCRYPTO_BAD_ARGS, OTCRYPTO_RECOV_ERR, OTCRYPTO_FATAL_ERR,
      OTCRYPTO_ASYNC_INCOMPLETE, OTCRYPTO_NOT_IMPLEMENTED};

  // Expect the "OK" code to have a significant Hamming distance from 0.
  EXPECT_GE(HammingDistance(kCryptoStatusOK, 0), kMinimumHammingDistance)
      << "The 'OK' status code " << kCryptoStatusOK << " is too close to zero.";

  for (const crypto_status_t status1 : error_codes) {
    // Expect a significant Hamming distance from 0.
    EXPECT_GE(HammingDistance(status1.value, 0), kMinimumHammingDistance)
        << "Error code " << status1.value << " is too close to zero.";
    // Expect an extra significant Hamming distance from the "OK" code.
    EXPECT_GE(HammingDistance(status1.value, kCryptoStatusOK),
              kMinimumHammingDistance)
        << "Error code " << status1.value << " is too close to the 'OK' value ("
        << kCryptoStatusOK << ").";

    // Expect a significant Hamming distance from all other error codes.
    for (const crypto_status_t status2 : error_codes) {
      if (status1.value != status2.value) {
        EXPECT_GE(HammingDistance(status1.value, status2.value),
                  kMinimumHammingDistance)
            << "Error codes " << status1.value << " and " << status2.value
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
  EXPECT_EQ(status_ok(OTCRYPTO_NOT_IMPLEMENTED), false);
}

TEST(Status, ErrorMacrosHaveExpectedValues) {
  // Error macros should evaluate to specific Abseil error codes.
  EXPECT_EQ(status_err(OTCRYPTO_BAD_ARGS), kInvalidArgument);
  EXPECT_EQ(status_err(OTCRYPTO_RECOV_ERR), kAborted);
  EXPECT_EQ(status_err(OTCRYPTO_FATAL_ERR), kFailedPrecondition);
  EXPECT_EQ(status_err(OTCRYPTO_ASYNC_INCOMPLETE), kUnavailable);
  EXPECT_EQ(status_err(OTCRYPTO_NOT_IMPLEMENTED), kUnimplemented);
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

TEST(Status, TryInterpretErrors) {
  // Error macros should result in error statuses.
  EXPECT_EQ(status_ok(try_interpret(OTCRYPTO_BAD_ARGS)), false);
  EXPECT_EQ(status_ok(try_interpret(OTCRYPTO_RECOV_ERR)), false);
  EXPECT_EQ(status_ok(try_interpret(OTCRYPTO_FATAL_ERR)), false);
  EXPECT_EQ(status_ok(try_interpret(OTCRYPTO_ASYNC_INCOMPLETE)), false);
}

}  // namespace
}  // namespace status_unittest
