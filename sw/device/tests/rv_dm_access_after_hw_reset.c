// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_utils.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/*
  - Wait for host to perform debugger tests
  - Once the host side confirms, do a SW reset of the chip
  - Print a message to confirm reset to host
  - Host will attach debugger and perform additional checks
 */

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

static volatile uint8_t kReset = 0;

enum {
  kTestTimeoutMicros = 1000000,  // 1 second
};

static dif_rstmgr_t rstmgr;

/**
 * Resets the chip.
 */
static void chip_sw_reset(void) {
  CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));
  busy_spin_micros(100);
  CHECK(false, "Should have reset before this line");
}

bool test_main(void) {
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));

  // Check if there was a HW reset caused by the software.
  dif_rstmgr_reset_info_bitfield_t rst_info;
  rst_info = rstmgr_testutils_reason_get();
  rstmgr_testutils_reason_clear();

  if (rst_info & kDifRstmgrResetInfoPor) {
    LOG_INFO("Waiting for commands");
    OTTF_WAIT_FOR(kReset != 0, kTestTimeoutMicros);

    chip_sw_reset();
    return false;

  } else if (rst_info & kDifRstmgrResetInfoSw) {
    LOG_INFO("Reset complete");
    return true;

  } else {
    LOG_ERROR("Unexpected reset info %d", rst_info);
  }

  return false;
}
