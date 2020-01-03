// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

extern "C" {
#include "sw/device/lib/dif/dif_spi_device.h"
}

#include "sw/device/lib/dif/testing/fixture.h"
#include "sw/device/lib/dif/testing/mock_mmio.h"

using dif_test::AccessType;
using dif_test::DifTest;
using dif_test::MockDevice;

bool _ = DifTest::NewTest("SmokeCheck", [] {
  MockDevice device{{
      {AccessType::kRead, 0x0000000c, 0xffffffff},
      {AccessType::kWrite, 0x0000000c, 0xfffffffe},
      {AccessType::kWrite, 0x00000010, 0x00000000},
      {AccessType::kWrite, 0x00000028, 0x03ff0000},
      {AccessType::kWrite, 0x0000002c, 0x07ff0600},

      {AccessType::kRead, 0x00000000, 0x00000000},
      {AccessType::kRead, 0x00000000, 0x00000000},
      {AccessType::kWrite, 0x00000000, 0x00000000},
      {AccessType::kWrite, 0x00000000, 0x00000000},
      {AccessType::kWrite, 0x00000000, 0x00000000},
  }};
  dif_spi_device_config_t conf{&device};
  dif_spi_device_t spi;

  dif_spi_device_init(conf, &spi);
  dif_spi_device_send(&spi, "xyz", 3);

  return device;
});

int main() { return DifTest::RunAll(); }
