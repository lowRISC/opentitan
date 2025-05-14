// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/mock_rnd.h"

namespace rom_test {
extern "C" {
rom_error_t rnd_health_config_check(lifecycle_state_t lc_state) {
  return MockRnd::Instance().HealthConfigCheck(lc_state);
}

uint32_t rnd_uint32(void) { return MockRnd::Instance().Uint32(); }

// For masking randomness, the value shouldn't matter; return constants.
uint32_t hardened_memshred_random_word(void) { return 0xdeadbeef; }
uint32_t random_order_random_word(void) { return 0xc0ffee11; }
}
}  // namespace rom_test
