// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static dif_rstmgr_t rstmgr;

OTTF_DEFINE_TEST_CONFIG(.enable_concurrency = false,
                        .can_clobber_uart = false, );

bool test_main(void) {
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));

  if (rstmgr_testutils_is_reset_info(&rstmgr, kDifRstmgrResetInfoPor)) {
    rstmgr_testutils_reason_clear();

    // Sync log used by the SV sequence. Do not modify.
    LOG_INFO("Ready for CPU halt request");

    // Wait for 1ms. The host test sequence will issue a halt request, followed
    // by an NDM reset request.
    busy_spin_micros(10000);

    LOG_ERROR("Timed out waiting for an NDM reset request.");
    return false;

  } else if (rstmgr_testutils_is_reset_info(&rstmgr, kDifRstmgrResetInfoNdm)) {
    LOG_INFO("Rebooted after NDM reset request.");
    rstmgr_testutils_reason_clear();
    return true;

  } else {
    dif_rstmgr_reset_info_bitfield_t reset_info;
    reset_info = rstmgr_testutils_reason_get();
    LOG_ERROR("Unexpected reset_info: %d", reset_info);
    return false;
  }

  return false;
}
