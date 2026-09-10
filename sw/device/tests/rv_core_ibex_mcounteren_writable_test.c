// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Verifies that the mcounteren_writable register properly locks the mcounteren
// CSR and that the register is write-protected when locked.

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top/rv_core_ibex_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define MCOUNTERS_DISABLE (0x0)
#define MCOUNTERS_ENABLE (0x5)

OTTF_DEFINE_TEST_CONFIG();

// Helper functions for accessing the mcounteren CSR
static inline uint32_t csr_read_mcounteren(void) {
  uint32_t val;
  asm volatile("csrr %0, mcounteren" : "=r"(val));
  return val;
}

static inline void csr_write_mcounteren(uint32_t val) {
  asm volatile("csrw mcounteren, %0" ::"r"(val));
}

bool test_main(void) {
  uint32_t mcounteren_val;
  uint32_t mcounteren_writable_val;
  uint32_t regwen;

  mmio_region_t ibex_cfg =
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR);

  // Initialize mcounteren to a known value for testing.
  csr_write_mcounteren(MCOUNTERS_DISABLE);

  // Check defaults
  // MCOUNTEREN_WRITABLE should default to kMultiBitBool4True.
  mcounteren_writable_val =
      mmio_region_read32(ibex_cfg, RV_CORE_IBEX_MCOUNTEREN_WRITABLE_REG_OFFSET);
  CHECK(mcounteren_writable_val == kMultiBitBool4True,
        "MCOUNTEREN_WRITABLE default should be MuBi4True (0x%x), got 0x%x",
        kMultiBitBool4True, mcounteren_writable_val);
  // REGWEN should be enabled by default.
  regwen = mmio_region_read32(
      ibex_cfg, RV_CORE_IBEX_MCOUNTEREN_WRITABLE_REGWEN_REG_OFFSET);
  CHECK(regwen == 1, "MCOUNTEREN_WRITABLE_REGWEN default should be 1, got 0x%x",
        regwen);

  // Since MCOUNTEREN_WRITABLE is True, writes to mcounteren should succeed.
  csr_write_mcounteren(MCOUNTERS_ENABLE);
  mcounteren_val = csr_read_mcounteren();
  CHECK(mcounteren_val == MCOUNTERS_ENABLE,
        "mcounteren should be writable when MCOUNTEREN_WRITABLE is True. "
        "Expected 0x%x, got 0x%x",
        MCOUNTERS_ENABLE, mcounteren_val);

  // Locking should succeed while REGWEN is enabled.
  mmio_region_write32(ibex_cfg, RV_CORE_IBEX_MCOUNTEREN_WRITABLE_REG_OFFSET,
                      kMultiBitBool4False);
  mcounteren_writable_val =
      mmio_region_read32(ibex_cfg, RV_CORE_IBEX_MCOUNTEREN_WRITABLE_REG_OFFSET);
  CHECK(mcounteren_writable_val == kMultiBitBool4False,
        "MCOUNTEREN_WRITABLE write should succeed when unlocked, got 0x%x",
        mcounteren_writable_val);

  // Since MCOUNTEREN_WRITABLE is now False, writes to mcounteren should be
  // ignored.
  csr_write_mcounteren(MCOUNTERS_DISABLE);
  mcounteren_val = csr_read_mcounteren();
  CHECK(mcounteren_val == MCOUNTERS_ENABLE,
        "mcounteren writes should be blocked when MCOUNTEREN_WRITABLE is "
        "False. Expected 0x%x, got 0x%x",
        MCOUNTERS_ENABLE, mcounteren_val);

  // Unlocking should succeed while REGWEN is enabled.
  mmio_region_write32(ibex_cfg, RV_CORE_IBEX_MCOUNTEREN_WRITABLE_REG_OFFSET,
                      kMultiBitBool4True);
  mcounteren_writable_val =
      mmio_region_read32(ibex_cfg, RV_CORE_IBEX_MCOUNTEREN_WRITABLE_REG_OFFSET);
  CHECK(mcounteren_writable_val == kMultiBitBool4True,
        "MCOUNTEREN_WRITABLE write should succeed when unlocked, got 0x%x",
        mcounteren_writable_val);

  // Ensure mcounteren is writable again after restoring MCOUNTEREN_WRITABLE to
  // True.
  csr_write_mcounteren(MCOUNTERS_DISABLE);
  mcounteren_val = csr_read_mcounteren();
  CHECK(mcounteren_val == MCOUNTERS_DISABLE,
        "mcounteren should be writable again after restoring config. Expected "
        "0x%x, got 0x%x",
        MCOUNTERS_DISABLE, mcounteren_val);

  // Enable mcounteren again.
  csr_write_mcounteren(MCOUNTERS_ENABLE);
  mcounteren_val = csr_read_mcounteren();
  CHECK(mcounteren_val == MCOUNTERS_ENABLE,
        "mcounteren should be writable again after restoring config. Expected "
        "0x%x, got 0x%x",
        MCOUNTERS_ENABLE, mcounteren_val);

  // Lock again, which should succeed.
  mmio_region_write32(ibex_cfg, RV_CORE_IBEX_MCOUNTEREN_WRITABLE_REG_OFFSET,
                      kMultiBitBool4False);
  mcounteren_writable_val =
      mmio_region_read32(ibex_cfg, RV_CORE_IBEX_MCOUNTEREN_WRITABLE_REG_OFFSET);
  CHECK(mcounteren_writable_val == kMultiBitBool4False,
        "MCOUNTEREN_WRITABLE write should succeed when unlocked, got 0x%x",
        mcounteren_writable_val);

  // Clear REGWEN to lock MCOUNTEREN_WRITABLE.
  mmio_region_write32(ibex_cfg,
                      RV_CORE_IBEX_MCOUNTEREN_WRITABLE_REGWEN_REG_OFFSET, 0);
  regwen = mmio_region_read32(
      ibex_cfg, RV_CORE_IBEX_MCOUNTEREN_WRITABLE_REGWEN_REG_OFFSET);
  CHECK(regwen == 0,
        "MCOUNTEREN_WRITABLE_REGWEN should read 0 after clearing, got 0x%x",
        regwen);

  // Write to MCOUNTEREN_WRITABLE while locked should have no effect.
  mmio_region_write32(ibex_cfg, RV_CORE_IBEX_MCOUNTEREN_WRITABLE_REG_OFFSET,
                      kMultiBitBool4True);
  mcounteren_writable_val =
      mmio_region_read32(ibex_cfg, RV_CORE_IBEX_MCOUNTEREN_WRITABLE_REG_OFFSET);
  CHECK(mcounteren_writable_val == kMultiBitBool4False,
        "MCOUNTEREN_WRITABLE should be unchanged when locked, got 0x%x",
        mcounteren_writable_val);

  // Since the attempt to flip MCOUNTEREN_WRITABLE to True was
  // ignored, writes to mcounteren should be ignored.
  csr_write_mcounteren(MCOUNTERS_DISABLE);
  mcounteren_val = csr_read_mcounteren();
  CHECK(mcounteren_val == MCOUNTERS_ENABLE,
        "mcounteren writes should be blocked when MCOUNTEREN_WRITABLE is "
        "False. Expected 0x%x, got 0x%x",
        MCOUNTERS_ENABLE, mcounteren_val);

  // Attempt to re-enable REGWEN should fail
  mmio_region_write32(ibex_cfg,
                      RV_CORE_IBEX_MCOUNTEREN_WRITABLE_REGWEN_REG_OFFSET, 1);
  regwen = mmio_region_read32(
      ibex_cfg, RV_CORE_IBEX_MCOUNTEREN_WRITABLE_REGWEN_REG_OFFSET);
  CHECK(regwen == 0,
        "MCOUNTEREN_WRITABLE_REGWEN should remain 0 after attempted "
        "re-enable, got 0x%x",
        regwen);

  // Write to MCOUNTEREN_WRITABLE while locked should have no effect.
  mmio_region_write32(ibex_cfg, RV_CORE_IBEX_MCOUNTEREN_WRITABLE_REG_OFFSET,
                      kMultiBitBool4True);
  mcounteren_writable_val =
      mmio_region_read32(ibex_cfg, RV_CORE_IBEX_MCOUNTEREN_WRITABLE_REG_OFFSET);
  CHECK(mcounteren_writable_val == kMultiBitBool4False,
        "MCOUNTEREN_WRITABLE should be unchanged when locked, got 0x%x",
        mcounteren_writable_val);

  return true;
}
