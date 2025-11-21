// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/ibex.h"

#include "hw/top/dt/dt_rv_core_ibex.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"

#include "hw/top/rv_core_ibex_regs.h"

static const dt_rv_core_ibex_t kRvCoreIbexDt = kDtRvCoreIbex;

void ibex_mcycle_zero(void) {
  CSR_WRITE(CSR_REG_MCYCLE, 0);
  CSR_WRITE(CSR_REG_MCYCLEH, 0);
}

uint32_t ibex_mcycle32(void) {
  uint32_t val;
  CSR_READ(CSR_REG_MCYCLE, &val);
  return val;
}

uint64_t ibex_mcycle(void) {
  uint32_t lo, hi, hi2;
  do {
    CSR_READ(CSR_REG_MCYCLEH, &hi);
    CSR_READ(CSR_REG_MCYCLE, &lo);
    CSR_READ(CSR_REG_MCYCLEH, &hi2);
  } while (hi != hi2);
  return ((uint64_t)hi << 32) | lo;
}

uint64_t ibex_time_to_cycles(uint64_t time_us) {
  return to_cpu_cycles(time_us);
}

/**
 * Base address of the rv_core_ibex registers.
 *
 */
static inline uint32_t rv_core_ibex_base(void) {
  return dt_rv_core_ibex_reg_block(kRvCoreIbexDt, kDtRvCoreIbexRegBlockCfg);
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

uint32_t ibex_rnd32_read(void) {
  wait_rnd_valid();
  return abs_mmio_read32(rv_core_ibex_base() +
                         RV_CORE_IBEX_RND_DATA_REG_OFFSET);
}

uint32_t ibex_fpga_version(void) {
  const uint32_t kBase = rv_core_ibex_base();
  return abs_mmio_read32(kBase + RV_CORE_IBEX_FPGA_INFO_REG_OFFSET);
}

size_t ibex_addr_remap_slots(void) { return RV_CORE_IBEX_PARAM_NUM_REGIONS; }

void ibex_addr_remap_set(size_t slot, uint32_t matching_addr,
                         uint32_t remap_addr, size_t size) {
  HARDENED_CHECK_LT(slot, RV_CORE_IBEX_PARAM_NUM_REGIONS);
  const uint32_t kBase = rv_core_ibex_base();
  slot *= sizeof(uint32_t);
  // Work-around for opentitan#22884: Mask off bits below the alignment size
  // prior to programming the REMAP_ADDR register.
  size = size - 1;
  uint32_t match = (matching_addr & ~size) | size >> 1;
  remap_addr &= ~size;

  sec_mmio_write32(kBase + RV_CORE_IBEX_IBUS_ADDR_MATCHING_0_REG_OFFSET + slot,
                   match);
  sec_mmio_write32(kBase + RV_CORE_IBEX_DBUS_ADDR_MATCHING_0_REG_OFFSET + slot,
                   match);

  sec_mmio_write32(kBase + RV_CORE_IBEX_IBUS_REMAP_ADDR_0_REG_OFFSET + slot,
                   remap_addr);
  sec_mmio_write32(kBase + RV_CORE_IBEX_DBUS_REMAP_ADDR_0_REG_OFFSET + slot,
                   remap_addr);

  sec_mmio_write32(kBase + RV_CORE_IBEX_IBUS_ADDR_EN_0_REG_OFFSET + slot, 1);
  sec_mmio_write32(kBase + RV_CORE_IBEX_DBUS_ADDR_EN_0_REG_OFFSET + slot, 1);
  icache_invalidate();
}

uint32_t ibex_addr_remap_get(size_t slot) {
  const uint32_t kBase = rv_core_ibex_base();
  HARDENED_CHECK_LT(slot, RV_CORE_IBEX_PARAM_NUM_REGIONS);
  slot *= sizeof(uint32_t);
  if (abs_mmio_read32(kBase + RV_CORE_IBEX_IBUS_ADDR_EN_0_REG_OFFSET + slot)) {
    return abs_mmio_read32(kBase + RV_CORE_IBEX_IBUS_REMAP_ADDR_0_REG_OFFSET +
                           slot);
  } else {
    return 0;
  }
}

void ibex_addr_remap_lockdown(size_t slot) {
  const uint32_t kBase = rv_core_ibex_base();
  HARDENED_CHECK_LT(slot, RV_CORE_IBEX_PARAM_NUM_REGIONS);
  slot *= sizeof(uint32_t);
  sec_mmio_write32(kBase + RV_CORE_IBEX_IBUS_REGWEN_0_REG_OFFSET + slot, 0);
  sec_mmio_write32(kBase + RV_CORE_IBEX_DBUS_REGWEN_0_REG_OFFSET + slot, 0);
}

bool ibex_addr_remap_is_enabled(size_t slot) {
  const uint32_t kBase = rv_core_ibex_base();
  HARDENED_CHECK_LT(slot, RV_CORE_IBEX_PARAM_NUM_REGIONS);
  slot *= sizeof(uint32_t);

  uint32_t reg_en_i =
      sec_mmio_read32(kBase + RV_CORE_IBEX_IBUS_ADDR_EN_0_REG_OFFSET + slot);
  uint32_t reg_en_i_mask = 1 << RV_CORE_IBEX_DBUS_ADDR_EN_0_EN_0_BIT;
  uint32_t reg_en_d =
      sec_mmio_read32(kBase + RV_CORE_IBEX_DBUS_ADDR_EN_0_REG_OFFSET + slot);
  uint32_t reg_en_d_mask = 1 << RV_CORE_IBEX_IBUS_ADDR_EN_0_EN_0_BIT;

  return (reg_en_i & reg_en_i_mask) && (reg_en_d & reg_en_d_mask);
}

static bool remap_verify(uint32_t reg_matching, uint32_t reg_remap,
                         uint32_t matching_addr, uint32_t remap_addr,
                         size_t size) {
  /* Check that matching register is non-zero
   * (otherwise the NAPOT formula below does not work) */
  if (reg_matching == 0) {
    return false;
  }

  /* decode NAPOT encoding */
  uint32_t reg_matching_size =
      1 << bitfield_count_trailing_zeroes32(~reg_matching);
  uint32_t reg_matching_addr = reg_matching & ~(reg_matching_size - 1);

  /* Check that the matching address is within the remap range */
  if (matching_addr < reg_matching_addr ||
      matching_addr - reg_matching_addr >= reg_matching_size) {
    return false;
  }

  /* We know that the matching address is withing the remap range, we can now
     safely check for the size validity */
  if (size > reg_matching_size - (matching_addr - reg_matching_addr)) {
    return false;
  }

  /* Check that remapping offset is identical */
  if (remap_addr - matching_addr != reg_remap - reg_matching_addr) {
    return false;
  }

  return true;
}

bool ibex_addr_remap_verify(size_t slot, uint32_t matching_addr,
                            uint32_t remap_addr, size_t size) {
  const uint32_t kBase = rv_core_ibex_base();
  HARDENED_CHECK_LT(slot, RV_CORE_IBEX_PARAM_NUM_REGIONS);
  slot *= sizeof(uint32_t);

  /* Check IBUS remapping */
  uint32_t reg_matching = sec_mmio_read32(
      kBase + RV_CORE_IBEX_IBUS_ADDR_MATCHING_0_REG_OFFSET + slot);
  uint32_t reg_remap_addr =
      sec_mmio_read32(kBase + RV_CORE_IBEX_IBUS_REMAP_ADDR_0_REG_OFFSET + slot);
  if (!remap_verify(reg_matching, reg_remap_addr, matching_addr, remap_addr,
                    size)) {
    return false;
  }

  /* Check DBUS remapping */
  reg_matching = sec_mmio_read32(
      kBase + RV_CORE_IBEX_DBUS_ADDR_MATCHING_0_REG_OFFSET + slot);
  reg_remap_addr =
      sec_mmio_read32(kBase + RV_CORE_IBEX_DBUS_REMAP_ADDR_0_REG_OFFSET + slot);
  if (!remap_verify(reg_matching, reg_remap_addr, matching_addr, remap_addr,
                    size)) {
    return false;
  }

  return true;
}

void ibex_enable_nmi(ibex_nmi_source_t nmi_src) {
  abs_mmio_write32(rv_core_ibex_base() + RV_CORE_IBEX_NMI_ENABLE_REG_OFFSET,
                   nmi_src);
}

void ibex_clear_nmi(ibex_nmi_source_t nmi_src) {
  abs_mmio_write32(rv_core_ibex_base() + RV_CORE_IBEX_NMI_STATE_REG_OFFSET,
                   nmi_src);
}
