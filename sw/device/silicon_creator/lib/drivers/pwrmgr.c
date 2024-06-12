// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/pwrmgr.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/ibex.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "pwrmgr_regs.h"

enum {
  kBase = TOP_EARLGREY_PWRMGR_AON_BASE_ADDR,
  kAllResetsEnable = (1 << kTopEarlgreyPowerManagerResetRequestsLast) - 1,
  kSyncConfig = (1 << PWRMGR_CFG_CDC_SYNC_SYNC_BIT),
};

static_assert(kAllResetsEnable == 0x1,
              "Number of reset requests changed, update expectation if this is "
              "intentional");
static_assert(
    PWRMGR_RESET_EN_EN_FIELD_WIDTH == 1,
    "RESET_EN field width changed, kAllResetsEnable may need to be updated");

void pwrmgr_cdc_sync(uint32_t n) {
  // We want to timeout if the CDC bit doesn't self clear.  It should take
  // approximately 4 AON ticks to complete.  We wait 25% longer (5 ticks).
  uint32_t cpu_cycle_timeout =
      (uint32_t)kClockFreqCpuHz / (uint32_t)kClockFreqAonHz * 5;

  // Ensure the bit is clear before requesting another sync.
  ibex_mcycle_zero();
  while (abs_mmio_read32(kBase + PWRMGR_CFG_CDC_SYNC_REG_OFFSET)) {
    if (ibex_mcycle32() > cpu_cycle_timeout) {
      // If the sync bit isn't clear, we shouldn't set it again.  Abort.
      return;
    }
  }
  // Perform the sync procedure the requested number of times.
  while (n--) {
    ibex_mcycle_zero();
    abs_mmio_write32(kBase + PWRMGR_CFG_CDC_SYNC_REG_OFFSET, kSyncConfig);
    while (abs_mmio_read32(kBase + PWRMGR_CFG_CDC_SYNC_REG_OFFSET)) {
      if (ibex_mcycle32() > cpu_cycle_timeout)
        // If the sync bit isn't clear, we shouldn't set it again.  Abort.
        return;
    }
  }
}

void pwrmgr_all_resets_enable(void) {
  SEC_MMIO_ASSERT_WRITE_INCREMENT(kPwrmgrSecMmioAllResetsEnable, 1);
  // Enable all resets.
  sec_mmio_write32(kBase + PWRMGR_RESET_EN_REG_OFFSET, kAllResetsEnable);
  pwrmgr_cdc_sync(1);
}
