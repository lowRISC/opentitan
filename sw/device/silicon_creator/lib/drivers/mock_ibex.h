// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_IBEX_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_IBEX_H_

#include "sw/device/lib/base/global_mock.h"
#include "sw/device/silicon_creator/lib/drivers/ibex.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace rom_test {
namespace internal {

/**
 * Mock class for ibex.c.
 */
class MockIbex : public global_mock::GlobalMock<MockIbex> {
 public:
  MOCK_METHOD(uint32_t, Rnd32, ());
  MOCK_METHOD(uint32_t, MCycle32, ());
  MOCK_METHOD(uint64_t, MCycle, ());
  MOCK_METHOD(void, MCycleZero, ());
  MOCK_METHOD(uint64_t, IbexTimeToCycles, (uint64_t time_us));
};

}  // namespace internal

using MockIbex = testing::StrictMock<internal::MockIbex>;

}  // namespace rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_IBEX_H_
