// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static dif_rstmgr_t rstmgr;

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));

  dif_rstmgr_reset_info_bitfield_t info;
  CHECK_DIF_OK(dif_rstmgr_reset_info_get(&rstmgr, &info));

  // If POR, clear reason and request software reset
  if (info & kDifRstmgrResetInfoPor) {
    LOG_INFO("POR encountered!");
    CHECK_DIF_OK(dif_rstmgr_reset_info_clear(&rstmgr));
    CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));

    // wait here until device reset
    wait_for_interrupt();
  } else if (info == kDifRstmgrResetInfoSw) {
    LOG_INFO("Software reset encountered!");
    CHECK_DIF_OK(dif_rstmgr_reset_info_clear(&rstmgr));
  } else {
    LOG_FATAL("Reset reason unexpected!");
    test_status_set(kTestStatusFailed);
  }

  return true;
}
