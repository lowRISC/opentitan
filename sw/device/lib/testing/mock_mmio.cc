// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/mock_mmio.h"

#include "sw/device/lib/base/mmio.h"

namespace mock_mmio {
std::random_device MockDevice::rd;

// Definitions for the MOCK_MMIO-mode declarations in |mmio.h|.
extern "C" {
// dummy
mmio_region_t mmio_region_from_addr(uintptr_t address) {
  return (mmio_region_t){};
}

uint8_t mmio_region_read8(mmio_region_t base, ptrdiff_t offset) {
  auto *dev = static_cast<MockDevice *>(base.mock);
  return dev->Read8(offset);
}

uint32_t mmio_region_read32(mmio_region_t base, ptrdiff_t offset) {
  auto *dev = static_cast<MockDevice *>(base.mock);
  return dev->Read32(offset);
}

void mmio_region_write8(mmio_region_t base, ptrdiff_t offset, uint8_t value) {
  auto *dev = static_cast<MockDevice *>(base.mock);
  dev->Write8(offset, value);
}

void mmio_region_write32(mmio_region_t base, ptrdiff_t offset, uint32_t value) {
  auto *dev = static_cast<MockDevice *>(base.mock);
  dev->Write32(offset, value);
}
}  // extern "C"
}  // namespace mock_mmio
