// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_RSTMGR_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_RSTMGR_H_

#include "sw/device/lib/base/global_mock.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"

namespace rom_test {
namespace internal {

/**
 * Mock class for rstmgr.c.
 */
class MockRstmgr : public global_mock::GlobalMock<MockRstmgr> {
 public:
  MOCK_METHOD(uint32_t, ReasonGet, ());
  MOCK_METHOD(void, ReasonClear, (uint32_t));
  MOCK_METHOD(void, AlertInfoEnable, ());
  MOCK_METHOD(void, Reset, ());
};

}  // namespace internal

using MockRstmgr = testing::StrictMock<internal::MockRstmgr>;

}  // namespace rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_RSTMGR_H_
