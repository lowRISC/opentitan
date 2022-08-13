// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/mock_spi_device.h"

namespace rom_test {
extern "C" {

void spi_device_init(void) { MockSpiDevice::Instance().Init(); }

rom_error_t spi_device_cmd_get(spi_device_cmd_t *cmd) {
  return MockSpiDevice::Instance().CmdGet(cmd);
}

void spi_device_flash_status_clear(void) {
  MockSpiDevice::Instance().FlashStatusClear();
}

uint32_t spi_device_flash_status_get(void) {
  return MockSpiDevice::Instance().FlashStatusGet();
}

}  // extern "C"
}  // namespace rom_test
