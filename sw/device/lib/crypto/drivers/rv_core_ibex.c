// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/rv_core_ibex.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/macros.h"

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

OT_ALWAYS_INLINE void ibex_clear_rf(void) {
#ifdef OT_PLATFORM_RV32
  // Invalidate the instruction cache.
  asm volatile("fence.i");
  // Get random word that gets written into the RF.
  uint32_t rnd = ibex_rnd32_read();
  // Skip x0 ... x4 as those register do not contain sensitive values.
  // x5 ... x31
  asm volatile("lw x5, 0(%0)" : : "r"(&rnd) : "x5");
  asm volatile("lw x6, 0(%0)" : : "r"(&rnd) : "x6");
  asm volatile("lw x7, 0(%0)" : : "r"(&rnd) : "x7");
  asm volatile("lw x8, 0(%0)" : : "r"(&rnd) : "x8");
  asm volatile("lw x9, 0(%0)" : : "r"(&rnd) : "x9");
  asm volatile("lw x10, 0(%0)" : : "r"(&rnd) : "x10");
  asm volatile("lw x11, 0(%0)" : : "r"(&rnd) : "x11");
  asm volatile("lw x12, 0(%0)" : : "r"(&rnd) : "x12");
  asm volatile("lw x13, 0(%0)" : : "r"(&rnd) : "x13");
  asm volatile("lw x14, 0(%0)" : : "r"(&rnd) : "x14");
  asm volatile("lw x15, 0(%0)" : : "r"(&rnd) : "x15");
  asm volatile("lw x16, 0(%0)" : : "r"(&rnd) : "x16");
  asm volatile("lw x17, 0(%0)" : : "r"(&rnd) : "x17");
  asm volatile("lw x18, 0(%0)" : : "r"(&rnd) : "x18");
  asm volatile("lw x19, 0(%0)" : : "r"(&rnd) : "x19");
  asm volatile("lw x20, 0(%0)" : : "r"(&rnd) : "x20");
  asm volatile("lw x21, 0(%0)" : : "r"(&rnd) : "x21");
  asm volatile("lw x22, 0(%0)" : : "r"(&rnd) : "x22");
  asm volatile("lw x23, 0(%0)" : : "r"(&rnd) : "x23");
  asm volatile("lw x24, 0(%0)" : : "r"(&rnd) : "x24");
  asm volatile("lw x25, 0(%0)" : : "r"(&rnd) : "x25");
  asm volatile("lw x26, 0(%0)" : : "r"(&rnd) : "x26");
  asm volatile("lw x27, 0(%0)" : : "r"(&rnd) : "x27");
  asm volatile("lw x28, 0(%0)" : : "r"(&rnd) : "x28");
  asm volatile("lw x29, 0(%0)" : : "r"(&rnd) : "x29");
  asm volatile("lw x30, 0(%0)" : : "r"(&rnd) : "x30");
  asm volatile("lw x31, 0(%0)" : : "r"(&rnd) : "x31");
#else  // OT_PLATFORM_RV32
  asm volatile("nop");
#endif
}

// Provides the source of randomness for `hardened_memshred` (see
// `hardened_memory.h`).
uint32_t hardened_memshred_random_word(void) { return ibex_rnd32_read(); }

// Provides the source of randomness for `random_order` (see `random_order.h`).
uint32_t random_order_random_word(void) { return ibex_rnd32_read(); }
