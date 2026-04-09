// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/crypto/drivers/rv_core_ibex.h"
#include "sw/device/lib/crypto/impl/status.h"

namespace test {
extern "C" {

hardened_bool_t ibex_check_security_config(void) { return kHardenedBoolTrue; }

status_t ibex_set_security_config(void) { return OTCRYPTO_OK; }

status_t ibex_disable_icache(hardened_bool_t *icache_enabled) {
  return OTCRYPTO_OK;
}

void ibex_restore_icache(hardened_bool_t icache_enabled) {
  asm volatile("nop");
}

// Since this mock library is for tests only, the randomness does not need to be
// real. https://xkcd.com/221/
uint32_t ibex_rnd32_read(void) { return 4; }

void ibex_clear_rf(void) { asm volatile("nop"); }

uint32_t hardened_memshred_random_word(void) { return ibex_rnd32_read(); }

uint32_t random_order_random_word(void) { return ibex_rnd32_read(); }
}
}  // namespace test
