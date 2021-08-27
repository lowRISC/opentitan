// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_LIFECYCLE_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_LIFECYCLE_H_

#include "sw/device/lib/testing/mask_rom_test.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"

namespace mask_rom_test {
namespace internal {

/**
 * Mock class for lifecycle.c.
 */
class MockLifecycle : public GlobalMock<MockLifecycle> {
 public:
  MOCK_METHOD(lifecycle_state_t, State, ());
  MOCK_METHOD(void, DeviceId, (lifecycle_device_id_t * device_id));
};

}  // namespace internal

using MockLifecycle = testing::StrictMock<internal::MockLifecycle>;

extern "C" {

lifecycle_state_t lifecycle_state_get(void) {
  return MockLifecycle::Instance().State();
}

void lifecycle_device_id_get(lifecycle_device_id_t *device_id) {
  MockLifecycle::Instance().DeviceId(device_id);
}

}  // extern "C"
}  // namespace mask_rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_LIFECYCLE_H_
