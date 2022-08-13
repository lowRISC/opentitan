// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_OTP_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_OTP_H_

#include "sw/device/lib/base/global_mock.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace rom_test {
namespace internal {

/**
 * Mock class for otp.c.
 */
class MockOtp : public global_mock::GlobalMock<MockOtp> {
 public:
  MOCK_METHOD(uint32_t, read32, (uint32_t address));
  MOCK_METHOD(uint32_t, read64, (uint32_t address));
  MOCK_METHOD(void, read, (uint32_t address, uint32_t *data, size_t num_words));
  MOCK_METHOD(void, CreatorSwCfgLockdown, ());
};

}  // namespace internal

// Nice mock for shutdown unit tests.
using NiceMockOtp = testing::NiceMock<internal::MockOtp>;
// Strict mock for other unit tests.
using MockOtp = testing::StrictMock<internal::MockOtp>;

}  // namespace rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_OTP_H_
