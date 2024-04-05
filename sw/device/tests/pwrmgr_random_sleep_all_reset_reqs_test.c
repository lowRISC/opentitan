// Copyright lowRISC contributors (OpenTitan project).
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

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

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

  uint32_t event_idx = 0;
  CHECK_STATUS_OK(ret_sram_testutils_counter_get(kCounterResets, &event_idx));
  CHECK_STATUS_OK(ret_sram_testutils_counter_increment(kCounterResets));

  int reset_case = event_idx / 2;
  bool deep_sleep = event_idx % 2 == 0;
  const char *sleep_mode = deep_sleep ? "deep" : "normal";
  pwrmgr_sleep_resets_lib_modes_t mode =
      deep_sleep ? kPwrmgrSleepResetsLibModesDeepSleep
                 : kPwrmgrSleepResetsLibModesNormalSleep;
  LOG_INFO("New reset event");
  LOG_INFO("  case %d, %s mode", reset_case, sleep_mode);

  switch (reset_case) {
    case 0:
      config_sysrst(kDeviceType == kDeviceSimDV ? kTopEarlgreyPinmuxInselIor13
                                                : kTopEarlgreyPinmuxInselIoc0);
      prepare_for_sysrst(mode);
      break;
    case 1:
      LOG_INFO("Watchdog reset in %s sleep mode", sleep_mode);
      LOG_INFO("Let SV wait timer reset");
      config_wdog(/*bark_micros=*/200, /*bite_micros=*/2 * 200);
      prepare_for_wdog(mode);
      break;
    case 2:
      LOG_INFO("Rstmgr software reset in %s sleep mode", sleep_mode);
      LOG_INFO("Let SV wait timer reset");
      // Triggering a sw reset will prevent the device from completing the
      // setup required to enter sleep mode. This sets a watchdog, but it will
      // most likely be wiped out by the software reset, unless they land in
      // very close temporal proximity.
      config_wdog(/*bark_micros=*/200, /*bite_micros=*/2 * 200);
      // Assert rstmgr software reset request.
      CHECK_DIF_OK(dif_rstmgr_software_device_reset(rstmgr));
      prepare_for_wdog(mode);
      break;
    case 3:
      LOG_INFO("Escalation reset in %s sleep mode", sleep_mode);
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
