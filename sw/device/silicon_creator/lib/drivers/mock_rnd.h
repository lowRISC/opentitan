// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_RND_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_RND_H_

#include "sw/device/silicon_creator/lib/drivers/rnd.h"
#include "sw/device/silicon_creator/testing/mask_rom_test.h"

namespace mask_rom_test {
namespace internal {

/**
 * Mock class for rnd.c.
 */
class MockRnd : public GlobalMock<MockRnd> {
 public:
  MOCK_METHOD(uint32_t, Uint32, ());
};

}  // namespace internal

using MockRnd = testing::StrictMock<internal::MockRnd>;

extern "C" {

uint32_t rnd_uint32(void) { return MockRnd::Instance().Uint32(); }

}  // extern "C"
}  // namespace mask_rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_RND_H_
