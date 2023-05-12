// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/hardened_status.h"

#include <vector>

#include "gmock/gmock.h"
#include "gtest/gtest.h"

// NOTE: This test does not verify hardening measures; it only checks that the
// "normal" contract of the functions is upheld.

namespace hardened_status_unittest {
namespace {

TEST(HardenedStatus, HardenedOkStatusIsOk) {
  EXPECT_EQ(status_ok(HARDENED_OK_STATUS), true);
}

TEST(HardenedStatus, HardenedOkStatusIsHardenedOk) {
  EXPECT_EQ(hardened_status_ok(HARDENED_OK_STATUS), kHardenedBoolTrue);
}

TEST(HardenedStatus, ErrorIsNotHardenedOk) {
  EXPECT_EQ(hardened_status_ok(INTERNAL()), kHardenedBoolFalse);
}

TEST(HardenedStatus, ErrorWithTruthyArgIsNotHardenedOk) {
  EXPECT_EQ(hardened_status_ok(INTERNAL(kHardenedBoolTrue)),
            kHardenedBoolFalse);
}

TEST(HardenedStatus, NormalOkIsNotHardenedOk) {
  EXPECT_EQ(hardened_status_ok(OK_STATUS()), kHardenedBoolFalse);
}

/**
 * Run `HARDENED_TRY` and return a non-hardened `OK` if it passes.
 *
 * @param status status code to try.
 */
__attribute__((noinline)) status_t do_hardened_try(status_t status) {
  HARDENED_TRY(status);
  return OK_STATUS();
}

TEST(HardenedStatus, HardenedTryOfNonHardenedOkIsError) {
  EXPECT_EQ(status_err(do_hardened_try(OK_STATUS())), kInternal);
}

TEST(HardenedStatus, HardenedTryOfHardenedOkIsOk) {
  EXPECT_EQ(status_ok(do_hardened_try(HARDENED_OK_STATUS)), true);
}

TEST(HardenedStatus, HardenedTryOfErrorIsError) {
  EXPECT_EQ(status_ok(do_hardened_try(INVALID_ARGUMENT())), false);
}

TEST(HardenedStatus, HardenedTryOfErrorWithTruthyArgIsError) {
  EXPECT_EQ(status_ok(do_hardened_try(INVALID_ARGUMENT(kHardenedBoolTrue))),
            false);
}

}  // namespace
}  // namespace hardened_status_unittest
