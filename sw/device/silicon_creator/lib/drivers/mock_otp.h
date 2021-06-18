// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_OTP_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_OTP_H_

#include "sw/device/lib/testing/mask_rom_test.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"

namespace mask_rom_test {
namespace internal {

/**
 * Mock class for otp.c.
 */
class MockOtp {
 public:
  MOCK_METHOD(uint32_t, read32, (uint32_t address));
  MOCK_METHOD(uint32_t, read64, (uint32_t address));
  MOCK_METHOD(void, read, (uint32_t address, uint32_t *data, size_t num_words));
  virtual ~MockOtp() {}
};

}  // namespace internal

using MockOtp = GlobalMock<testing::StrictMock<internal::MockOtp>>;

extern "C" {

uint32_t otp_read32(uint32_t address) {
  return MockOtp::Instance().read32(address);
}

uint64_t otp_read64(uint32_t address) {
  return MockOtp::Instance().read64(address);
}

void otp_read(uint32_t address, uint32_t *data, size_t num_words) {
  return MockOtp::Instance().read(address, data, num_words);
}

}  // extern "C"
}  // namespace mask_rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_OTP_H_
