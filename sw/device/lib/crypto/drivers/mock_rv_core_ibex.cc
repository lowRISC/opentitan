// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/rv_core_ibex.h"

namespace test {
extern "C" {

// Since this mock library is for tests only, the randomness does not need to be
// real. https://xkcd.com/221/
uint32_t ibex_rnd32_read(void) { return 4; }

uint32_t hardened_memshred_random_word(void) { return ibex_rnd32_read(); }

uint32_t random_order_random_word(void) { return ibex_rnd32_read(); }
}
}  // namespace test
