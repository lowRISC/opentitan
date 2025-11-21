// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_PWRMGR_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_PWRMGR_H_

#include "sw/device/lib/base/global_mock.h"
#include "sw/device/silicon_creator/lib/drivers/pwrmgr.h"

namespace rom_test {
namespace internal {

/**
 * Mock class for pwrmgr.c.
 */
class MockPwrmgr : public global_mock::GlobalMock<MockPwrmgr> {
 public:
  MOCK_METHOD(void, EnableWatchdogResetRequest, ());
  MOCK_METHOD(void, CdcSync, (uint32_t));
  MOCK_METHOD(void, AllResetsEnable, ());
};

}  // namespace internal

using MockPwrmgr = testing::StrictMock<internal::MockPwrmgr>;

}  // namespace rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_PWRMGR_H_
