// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/test_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

const test_config_t kTestConfig;

// When the test first runs the rstmgr's `reset_info` CSR should have the POR
// bit set, the code clears reset_info and calls wait_for_interrupt(). The WFI
// causes core_sleeping to rise, and that causes the SV side to glitch the main
// power rail, causing a pwrmgr internally generated reset. The next time the
// test runs is after the power glitch reset, which is confirmed reading the
// `reset_info` CSR.
bool test_main(void) {
  dif_rstmgr_t rstmgr;
  // This should be in some header file, but the number of hardware resets is
  // a parameter. This field is after 4 well known bits, some number of bits
  // that depend on the NumRstReqs parameter, and then there is MainPwr and
  // Esc (alation), in increasing order.
  //
  // TODO(maturana) Move this to dif_pwrmgr.h somehow dealing with params.
  const int kResetInfoMainPower = 6;

  // Initialize rstmgr since this will check some registers.
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));

  // Notice we are clearing rstmgr's RESET_INFO, so after the power glitch there
  // is only one bit set.

  if (rstmgr_testutils_is_reset_info(&rstmgr, kDifRstmgrResetInfoPor)) {
    LOG_INFO("Powered up for the first time, begin test");

    // Clear reset_info.
    CHECK_DIF_OK(dif_rstmgr_reset_info_clear(&rstmgr));

    // This causes core_sleeping to rise and triggers the injection of the
    // power glitch.
    wait_for_interrupt();

  } else if (rstmgr_testutils_is_reset_info(&rstmgr,
                                            1 << kResetInfoMainPower)) {
    LOG_INFO("Reset received for power glitch.");
    return true;

  } else {
    dif_rstmgr_reset_info_bitfield_t actual_info;
    CHECK_DIF_OK(dif_rstmgr_reset_info_get(&rstmgr, &actual_info));
    LOG_INFO("Unexpected reset_info contents: 0x%x", actual_info);
  }
  return false;
}
