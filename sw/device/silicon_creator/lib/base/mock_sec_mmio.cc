// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/base/mock_sec_mmio.h"

namespace rom_test {
extern "C" {
sec_mmio_ctx_t sec_mmio_ctx;

void sec_mmio_init(void) { MockSecMmio::Instance().Init(); }

uint32_t sec_mmio_read32(uint32_t addr) {
  return MockSecMmio::Instance().Read32(addr);
}

void sec_mmio_write32(uint32_t addr, uint32_t value) {
  MockSecMmio::Instance().Write32(addr, value);
}

void sec_mmio_write32_shadowed(uint32_t addr, uint32_t value) {
  MockSecMmio::Instance().Write32Shadowed(addr, value);
}

void sec_mmio_check_values(uint32_t rnd_offset) {
  MockSecMmio::Instance().CheckValues(rnd_offset);
}

void sec_mmio_check_counters(uint32_t expected_check_count) {
  MockSecMmio::Instance().CheckCounters(expected_check_count);
}
}  // extern "C"
}  // namespace rom_test
