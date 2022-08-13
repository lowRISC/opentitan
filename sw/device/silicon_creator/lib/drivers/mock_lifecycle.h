// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_LIFECYCLE_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_LIFECYCLE_H_

#include "sw/device/lib/base/global_mock.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace rom_test {
namespace internal {

/**
 * Mock class for lifecycle.c.
 */
class MockLifecycle : public global_mock::GlobalMock<MockLifecycle> {
 public:
  MOCK_METHOD(lifecycle_state_t, State, ());
  MOCK_METHOD(uint32_t, RawState, ());
  MOCK_METHOD(void, DeviceId, (lifecycle_device_id_t * device_id));
  MOCK_METHOD(void, HwRev, (lifecycle_hw_rev_t * hw_rev));
};

}  // namespace internal

using MockLifecycle = testing::StrictMock<internal::MockLifecycle>;

}  // namespace rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_LIFECYCLE_H_
