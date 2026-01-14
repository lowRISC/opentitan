// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  retention_sram_t *retram = retention_sram_get();

  bool redundancy_fixed = bitfield_bit32_read(retram->creator.boot_log.events,
                                              BOOT_LOG_EVENT_REDUNDANCY);
  LOG_INFO("Redundancy fix event: %d", redundancy_fixed);

  if (bitfield_bit32_read(retram->creator.reset_reasons,
                          kRstmgrReasonPowerOn)) {
    CHECK(redundancy_fixed, "ROM_EXT should fix redundancy on first boot");
    rstmgr_reset();
    return false;
  } else {
    CHECK(!redundancy_fixed, "It should already be fixed on the second boot");
    return true;
  }
}
