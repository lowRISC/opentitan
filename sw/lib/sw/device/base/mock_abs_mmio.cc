// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mock_abs_mmio.h"

namespace rom_test {
extern "C" {
uint8_t abs_mmio_read8(uint32_t addr) {
  return MockAbsMmio::Instance().Read8(addr);
}

void abs_mmio_write8(uint32_t addr, uint8_t value) {
  MockAbsMmio::Instance().Write8(addr, value);
}

void abs_mmio_write8_shadowed(uint32_t addr, uint8_t value) {
  MockAbsMmio::Instance().Write8Shadowed(addr, value);
}

uint32_t abs_mmio_read32(uint32_t addr) {
  return MockAbsMmio::Instance().Read32(addr);
}

void abs_mmio_write32(uint32_t addr, uint32_t value) {
  MockAbsMmio::Instance().Write32(addr, value);
}

void abs_mmio_write32_shadowed(uint32_t addr, uint32_t value) {
  MockAbsMmio::Instance().Write32Shadowed(addr, value);
}
}  // extern "C"
}  // namespace rom_test
