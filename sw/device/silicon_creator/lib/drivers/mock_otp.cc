// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/mock_otp.h"

namespace rom_test {
extern "C" {
// Note: In the functions below, we use `MockOtp` only for conciseness. The
// static `Instance()` method returns a reference to the same
// `internal::MockOtp` instance regardless if we use `MockOtp`, `NiceMockOtp`,
// or `internal::MockOtp`.
uint32_t otp_read32(uint32_t address) {
  return MockOtp::Instance().read32(address);
}

uint64_t otp_read64(uint32_t address) {
  return MockOtp::Instance().read64(address);
}

void otp_read(uint32_t address, uint32_t *data, size_t num_words) {
  return MockOtp::Instance().read(address, data, num_words);
}

void otp_creator_sw_cfg_lockdown(void) {
  MockOtp::Instance().CreatorSwCfgLockdown();
}
}  // extern "C"
}  // namespace rom_test
