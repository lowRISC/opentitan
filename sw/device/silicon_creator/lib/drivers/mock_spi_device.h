// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_SPI_DEVICE_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_SPI_DEVICE_H_

#include "sw/device/lib/base/global_mock.h"
#include "sw/device/silicon_creator/lib/drivers/spi_device.h"

namespace rom_test {
namespace internal {

/**
 * Mock class for spi_device.c.
 */
class MockSpiDevice : public global_mock::GlobalMock<MockSpiDevice> {
 public:
  MOCK_METHOD(void, Init, (uint8_t /*log2_density*/, const void *, size_t));
  MOCK_METHOD(void, InitBootstrap, ());
  MOCK_METHOD(rom_error_t, CmdGet, (spi_device_cmd_t *));
  MOCK_METHOD(void, FlashStatusClear, ());
  MOCK_METHOD(uint32_t, FlashStatusGet, ());
};

}  // namespace internal

using MockSpiDevice = testing::StrictMock<internal::MockSpiDevice>;
using NiceMockSpiDevice = testing::NiceMock<internal::MockSpiDevice>;

}  // namespace rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_SPI_DEVICE_H_
