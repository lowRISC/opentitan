// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/mock_ibex.h"

namespace rom_test {
extern "C" {
uint32_t ibex_mcycle32(void) { return MockIbex::Instance().MCycle32(); }
uint64_t ibex_mcycle(void) { return MockIbex::Instance().MCycle(); }
void ibex_mcycle_zero(void) { return MockIbex::Instance().MCycleZero(); }

uint64_t ibex_time_to_cycles(uint64_t time_us) {
  return MockIbex::Instance().IbexTimeToCycles(time_us);
}

uint32_t ibex_rnd32_read(void) { return MockIbex::Instance().Rnd32(); }
}
}  // namespace rom_test
