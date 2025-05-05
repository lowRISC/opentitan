// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/rv_core_ibex.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "rv_core_ibex_regs.h"

enum {
  kBaseAddr = TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR,
};

/**
 * Blocks until data is ready in the RND register.
 */
static void wait_rnd_valid(void) {
  while (true) {
    uint32_t reg =
        abs_mmio_read32(kBaseAddr + RV_CORE_IBEX_RND_STATUS_REG_OFFSET);
    if (bitfield_bit32_read(reg, RV_CORE_IBEX_RND_STATUS_RND_DATA_VALID_BIT)) {
      return;
    }
  }
}

uint32_t ibex_rnd32_read(void) {
  wait_rnd_valid();
  return abs_mmio_read32(kBaseAddr + RV_CORE_IBEX_RND_DATA_REG_OFFSET);
}

// Provides the source of randomness for `hardened_memshred` (see
// `hardened_memory.h`).
uint32_t hardened_memshred_random_word(void) { return ibex_rnd32_read(); }

// Provides the source of randomness for `random_order` (see `random_order.h`).
uint32_t random_order_random_word(void) { return ibex_rnd32_read(); }
