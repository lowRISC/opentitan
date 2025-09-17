// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/rv_core_ibex.h"

#include "hw/top/dt/dt_rv_core_ibex.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/crypto/impl/status.h"

#include "hw/top/rv_core_ibex_regs.h"

static const dt_rv_core_ibex_t kRvCoreIbexDt = kDtRvCoreIbex;

static inline uint32_t rv_core_ibex_base(void) {
  return dt_rv_core_ibex_primary_reg_block(kRvCoreIbexDt);
}

enum {
  /**
   * CSR_REG_CPUCTRL[0] is the iCache configuration field.
   */
  kCpuctrlICacheMask = 1,
};

/**
 * Blocks until data is ready in the RND register.
 */
static void wait_rnd_valid(void) {
  while (true) {
    uint32_t reg = abs_mmio_read32(rv_core_ibex_base() +
                                   RV_CORE_IBEX_RND_STATUS_REG_OFFSET);
    if (bitfield_bit32_read(reg, RV_CORE_IBEX_RND_STATUS_RND_DATA_VALID_BIT)) {
      return;
    }
  }
}

status_t ibex_disable_icache(hardened_bool_t *icache_enabled) {
  // Check if the instruction cache is already disabled.
  uint32_t csr;
  CSR_READ(CSR_REG_CPUCTRL, &csr);
  if ((csr & kCpuctrlICacheMask) == 1) {
    *icache_enabled = kHardenedBoolTrue;
  } else {
    *icache_enabled = kHardenedBoolFalse;
    HARDENED_CHECK_EQ(launder32((csr & kCpuctrlICacheMask)), 0);
  }

  // If the instruction cache is enabled, disable it.
  if (*icache_enabled == kHardenedBoolTrue) {
    CSR_CLEAR_BITS(CSR_REG_CPUCTRL, kCpuctrlICacheMask);
  } else {
    HARDENED_CHECK_EQ(launder32(*icache_enabled), kHardenedBoolFalse);
  }

  return OTCRYPTO_OK;
}

void ibex_restore_icache(hardened_bool_t icache_enabled) {
  // If the instruction cache was enabled before the CL disabled it, enable it
  // again.
  if (icache_enabled == kHardenedBoolTrue) {
    CSR_SET_BITS(CSR_REG_CPUCTRL, kCpuctrlICacheMask);
  }
}

uint32_t ibex_rnd32_read(void) {
  wait_rnd_valid();
  return abs_mmio_read32(rv_core_ibex_base() +
                         RV_CORE_IBEX_RND_DATA_REG_OFFSET);
}

// Provides the source of randomness for `hardened_memshred` (see
// `hardened_memory.h`).
uint32_t hardened_memshred_random_word(void) { return ibex_rnd32_read(); }

// Provides the source of randomness for `random_order` (see `random_order.h`).
uint32_t random_order_random_word(void) { return ibex_rnd32_read(); }
