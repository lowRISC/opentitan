// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

// When the test first runs the rstmgr's `reset_info` CSR should have the POR
// bit set, the code clears reset_info and calls wait_for_interrupt(). The WFI
// causes core_sleeping to rise, and that causes the SV side to glitch the main
// power rail, causing a pwrmgr internally generated reset. The next time the
// test runs is after the power glitch reset, which is confirmed reading the
// `reset_info` CSR.
bool test_main(void) {
  dif_rstmgr_t rstmgr;

  // Initialize rstmgr since this will check some registers.
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));

  // Notice we are clearing rstmgr's RESET_INFO, so after the power glitch there
  // is only one bit set.

  if (rstmgr_testutils_is_reset_info(&rstmgr, kDifRstmgrResetInfoPor)) {
    LOG_INFO("Powered up for the first time, begin test");

    rstmgr_testutils_pre_reset(&rstmgr);

    // This causes core_sleeping to rise and triggers the injection of the
    // power glitch. Notice it does not by itself trigger a low power
    // transition.
    wait_for_interrupt();

  } else {
    LOG_INFO("Checking reset status.");
    rstmgr_testutils_post_reset(&rstmgr, kDifRstmgrResetInfoPowerUnstable, 0, 0,
                                0, 0);
    LOG_INFO("Reset status indicates a main power glitch reset");
  }
  return true;
}
