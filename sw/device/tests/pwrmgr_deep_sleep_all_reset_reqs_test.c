// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <limits.h>
#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/ret_sram_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/FreeRTOSConfig.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/pwrmgr_sleep_resets_lib.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// In dvsim, one run
// with --waves can take
// 1.874h  | 38.068ms
// without --waves,
// 38.072m | 39.484ms

OTTF_DEFINE_TEST_CONFIG();

static const uint32_t kPlicTarget = kTopEarlgreyPlicTargetIbex0;

bool test_main(void) {
  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  init_peripherals();

  // Enable all the AON interrupts used in this test.
  rv_plic_testutils_irq_range_enable(plic, kPlicTarget,
                                     kTopEarlgreyPlicIrqIdAlertHandlerClassa,
                                     kTopEarlgreyPlicIrqIdAlertHandlerClassd);

  config_alert_handler();

  // Check if there was a HW reset caused by expected cases.
  dif_rstmgr_reset_info_bitfield_t rst_info;
  rst_info = rstmgr_testutils_reason_get();
  rstmgr_testutils_reason_clear();

  enum { kCounterResets = 0 };
  if (rst_info == kDifRstmgrResetInfoPor) {
    CHECK_STATUS_OK(ret_sram_testutils_counter_clear(kCounterResets));
  }
  CHECK_STATUS_OK(rstmgr_testutils_pre_reset(rstmgr));
  CHECK(rst_info == kDifRstmgrResetInfoPor ||
            rst_info == kDifRstmgrResetInfoSysRstCtrl ||
            rst_info == kDifRstmgrResetInfoWatchdog ||
            rst_info == kDifRstmgrResetInfoEscalation ||
            rst_info == kDifRstmgrResetInfoLowPowerExit ||
            rst_info == (kDifRstmgrResetInfoSysRstCtrl |
                         kDifRstmgrResetInfoLowPowerExit) ||
            rst_info ==
                (kDifRstmgrResetInfoPor | kDifRstmgrResetInfoLowPowerExit) ||
            rst_info == (kDifRstmgrResetInfoWatchdog |
                         kDifRstmgrResetInfoLowPowerExit) ||
            rst_info == (kDifRstmgrResetInfoEscalation |
                         kDifRstmgrResetInfoLowPowerExit) ||
            rst_info == kDifRstmgrResetInfoSw,
        "Wrong reset reason %02X", rst_info);

  uint32_t reset_case = 0;
  CHECK_STATUS_OK(ret_sram_testutils_counter_get(kCounterResets, &reset_case));
  CHECK_STATUS_OK(ret_sram_testutils_counter_increment(kCounterResets));
  LOG_INFO("New reset event");
  LOG_INFO("  case %d, deep sleep mode", reset_case);

  switch (reset_case) {
    case 0:
      LOG_INFO("Sysrst reset in deep sleep mode");
      config_sysrst(kDeviceType == kDeviceSimDV ? kTopEarlgreyPinmuxInselIor13
                                                : kTopEarlgreyPinmuxInselIoc0);
      enter_sleep_for_sysrst(/*deep_sleep=*/true);
      break;
    case 1:
      LOG_INFO("Watchdog reset in deep sleep mode");
      LOG_INFO("Let SV wait timer reset");
      CHECK_STATUS_OK(rstmgr_testutils_pre_reset(rstmgr));
      config_wdog(/*bark_micros=*/200, /*bite_micros=*/2 * 200);
      enter_sleep_for_wdog(/*deep_sleep=*/true);
      break;
    case 2:
      LOG_INFO("Rstmgr software reset in deep sleep mode");
      LOG_INFO("Let SV wait timer reset");
      CHECK_STATUS_OK(rstmgr_testutils_pre_reset(rstmgr));
      LOG_INFO("Device reset from sw");
      // Triggering a sw reset will prevent the device from completing the
      // setup required to enter sleep mode. This sets a watchdog, but it will
      // most likely be wiped out by the software reset, unless they land in
      // very close temporal proximity.
      config_wdog(/*bark_micros=*/200, /*bite_micros=*/2 * 200);
      // Assert rstmgr software reset request.
      CHECK_DIF_OK(dif_rstmgr_software_device_reset(rstmgr));
      enter_sleep_for_wdog(/*deep_sleep=*/true);
      break;
    case 3:
      LOG_INFO("Booting and running normal sleep followed by escalation reset");
      LOG_INFO("Let SV wait timer reset");
      trigger_escalation();
      break;
    case 4:
      LOG_INFO("Last Booting");
      return true;
    default:
      LOG_INFO("Booting for undefined case %0d", reset_case);
  }

  return false;
}
