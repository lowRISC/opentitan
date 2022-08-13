// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_MOCK_BOOT_DATA_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_MOCK_BOOT_DATA_H_

#include "sw/device/lib/base/global_mock.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace rom_test {
namespace internal {

/**
 * Mock class for boot_data.
 */
class MockBootData : public global_mock::GlobalMock<MockBootData> {
 public:
  MOCK_METHOD(rom_error_t, Read,
              (lifecycle_state_t lc_state, boot_data_t *boot_data));
  MOCK_METHOD(rom_error_t, Write, (const boot_data_t *boot_data));
  MOCK_METHOD(rom_error_t, Check, (const boot_data_t *boot_data));
};

}  // namespace internal

using MockBootData = testing::StrictMock<internal::MockBootData>;

}  // namespace rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_MOCK_BOOT_DATA_H_
