// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/base/rom_mmio.h"

uint32_t rom_mmio_read8(uint32_t addr) { return ((volatile uint8_t *)addr)[0]; }

void rom_mmio_write8(uint32_t addr, uint32_t value) {
  ((volatile uint8_t *)addr)[0] = value;
}

uint32_t rom_mmio_read32(uint32_t addr) {
  return ((volatile uint32_t *)addr)[0];
}

void rom_mmio_write32(uint32_t addr, uint32_t value) {
  ((volatile uint32_t *)addr)[0] = value;
}
