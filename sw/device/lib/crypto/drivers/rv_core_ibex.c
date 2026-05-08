// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/rv_core_ibex.h"

#include "hw/top/dt/rv_core_ibex.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
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
  /**
   * Mask for extracting cpuctrl_csr[1] and cpuctrl_csr[2] is 0b11.
   */
  kMask = 0x3,
  /**
   * The first item is cpuctrl_csr[1].
   */
  kIdx = 0x1,
  /**
   * cpuctrl_csr[1] and cpuctrl_csr[2] should be set to 0b11.
   */
  kExpectedConfig = 0x3,
};

hardened_bool_t ibex_check_security_config(void) {
  uint32_t cpuctrl_csr;
  CSR_READ(CSR_REG_CPUCTRL, &cpuctrl_csr);

  // Check if cpuctrl_csr[1] (data_ind_timing) and cpuctrl_csr[2]
  // (dummy_instr_en) is set to 1 (enabled).
  bitfield_field32_t cpuctrl_mask = {.mask = kMask, .index = kIdx};
  uint32_t cpuctrl_cfg = bitfield_field32_read(cpuctrl_csr, cpuctrl_mask);

  if (launder32(cpuctrl_cfg) != kExpectedConfig) {
    return kHardenedBoolFalse;
  }
  HARDENED_CHECK_EQ(cpuctrl_cfg, kExpectedConfig);

  return kHardenedBoolTrue;
}

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

OT_ALWAYS_INLINE void ibex_clear_rf(void) {
#ifdef OT_PLATFORM_RV32
  // ibex_clear_rf() below cannot clear x8 (frame pointer). To avoid that
  // x8 is not used for secret data, create a variable-length array (VLA).
  // This forces the compiler to use x8 instead of the stack pointer,
  // avoiding that x8 can be used for secret data.
  // Similarily, by forcing stack realignment (by having a large alignment),
  // x9 will also be reserved to avoid a similar problem as with x8.
  uint32_t dummy[launderw(0)][4] __attribute__((aligned(32)));
  barrierw((uintptr_t)&dummy);

  // Get random word that gets written into the RF.
  uint32_t rnd = ibex_rnd32_read();
  // Skip x0 ... x4 as those register do not contain sensitive values.
  // x5 ... x7
  asm volatile("lw x5, 0(%0)" : : "r"(&rnd) : "x5");
  asm volatile("lw x6, 0(%0)" : : "r"(&rnd) : "x6");
  asm volatile("lw x7, 0(%0)" : : "r"(&rnd) : "x7");
  // Skip x8/x9 as clobbering this register does not always
  // work, see llvm/llvm-project#157694.
  // x10 ... x31
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
