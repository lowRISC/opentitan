// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_SPI_HOST_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_SPI_HOST_H_

#include "sw/device/silicon_creator/lib/drivers/spi_host.h"
#include "sw/lib/sw/device/base/global_mock.h"

namespace rom_test {
namespace internal {

/**
 * Mock class for spi_host.c.
 */
class MockSpiHost : public global_mock::GlobalMock<MockSpiHost> {
 public:
  MOCK_METHOD(void, Init, (uint32_t));
  MOCK_METHOD(rom_error_t, Transaction,
              (uint32_t, const spi_host_segment_t *, size_t));
};

}  // namespace internal

using MockSpiHost = testing::StrictMock<internal::MockSpiHost>;

}  // namespace rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_SPI_HOST_H_
