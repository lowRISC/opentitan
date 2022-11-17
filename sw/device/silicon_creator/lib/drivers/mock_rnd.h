// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_RND_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_RND_H_

#include "sw/device/lib/base/global_mock.h"
#include "sw/device/silicon_creator/lib/drivers/rnd.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace rom_test {
namespace internal {

/**
 * Mock class for rnd.c.
 */
class MockRnd : public global_mock::GlobalMock<MockRnd> {
 public:
  MOCK_METHOD(rom_error_t, HealthConfigCheck, (lifecycle_state_t));
  MOCK_METHOD(uint32_t, Uint32, ());
};

}  // namespace internal

using MockRnd = testing::StrictMock<internal::MockRnd>;

}  // namespace rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_RND_H_
