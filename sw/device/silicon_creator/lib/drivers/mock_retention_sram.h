// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_RETENTION_SRAM_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_RETENTION_SRAM_H_

#include "sw/device/lib/base/global_mock.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace rom_test {
namespace internal {

/**
 * Mock class for retention_sram.c.
 */
class MockRetentionSram : public global_mock::GlobalMock<MockRetentionSram> {
 public:
  MOCK_METHOD(retention_sram_t *, Get, ());
};

}  // namespace internal

using MockRetentionSram = testing::StrictMock<internal::MockRetentionSram>;
using NiceMockRetentionSram = testing::NiceMock<internal::MockRetentionSram>;

}  // namespace rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_RETENTION_SRAM_H_
