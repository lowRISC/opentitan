// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_LIFECYCLE_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_LIFECYCLE_H_

#include "sw/device/lib/base/testing/global_mock.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/testing/mask_rom_test.h"

namespace mask_rom_test {
namespace internal {

/**
 * Mock class for lifecycle.c.
 */
class MockLifecycle : public global_mock::GlobalMock<MockLifecycle> {
 public:
  MOCK_METHOD(lifecycle_state_t, State, ());
  MOCK_METHOD(uint32_t, RawState, ());
  MOCK_METHOD(void, DeviceId, (lifecycle_device_id_t * device_id));
};

}  // namespace internal

using MockLifecycle = testing::StrictMock<internal::MockLifecycle>;

#ifdef IS_MESON_FOR_MIGRATIONS_ONLY
extern "C" {

lifecycle_state_t lifecycle_state_get(void) {
  return MockLifecycle::Instance().State();
}

uint32_t lifecycle_raw_state_get(void) {
  return MockLifecycle::Instance().RawState();
}

void lifecycle_device_id_get(lifecycle_device_id_t *device_id) {
  MockLifecycle::Instance().DeviceId(device_id);
}

}  // extern "C"
#endif
}  // namespace mask_rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_LIFECYCLE_H_
