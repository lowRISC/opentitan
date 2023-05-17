// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/pwrmgr.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"

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

void pwrmgr_all_resets_enable(void) {
  SEC_MMIO_ASSERT_WRITE_INCREMENT(kPwrmgrSecMmioAllResetsEnable, 1);
  // Enable all resets.
  sec_mmio_write32(kBase + PWRMGR_RESET_EN_REG_OFFSET, kAllResetsEnable);
  // Sync configuration across clock domains.
  // Note: This synchronization can take several clock cycles. Ideally we should
  // wait for the `SYNC` bit to clear but we don't do that since this is our
  // second try and we want to avoid loops as much as possible.
  abs_mmio_write32(kBase + PWRMGR_CFG_CDC_SYNC_REG_OFFSET, kSyncConfig);
}
