// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/freestanding/limits.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf.h"
#include "sw/device/lib/testing/test_framework/test_status.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define WDOG_BARK_TIME_US 1300
#define WDOG_BITE_TIME_US 1600
#define WKUP_TIME_US 2000
const test_config_t kTestConfig;

static uint64_t us_to_aon_cycles(uint64_t time_us) {
  return time_us * kClockFreqAonHz / 1000000;
}

static uint32_t cycles_to_32_bits(uint64_t cycles, const char *label) {
  CHECK(cycles < UINT32_MAX,
        "The %s value 0x%08x%08x can't fit into the 32 bits timer counter",
        label, (uint32_t)(cycles >> 32), (uint32_t)cycles);
  return (uint32_t)cycles;
}

bool test_main(void) {
  // Initialize pwrmgr.
  dif_pwrmgr_t pwrmgr;
  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));

  // Initialize rstmgr to check the reset reason.
  dif_rstmgr_t rstmgr;
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));

  // Initialize aon timer to use the wdog.
  dif_aon_timer_t aon_timer;
  CHECK_DIF_OK(dif_aon_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR), &aon_timer));

  // Enable aon_timer watchdog reset.
  // Set wdog as a reset source.
  CHECK_DIF_OK(dif_pwrmgr_set_request_sources(&pwrmgr, kDifPwrmgrReqTypeReset,
                                              kDifPwrmgrResetRequestSourceTwo,
                                              kDifToggleEnabled));

  // Check if there was a HW reset caused by the wdog bite.
  dif_rstmgr_reset_info_bitfield_t rst_info;
  CHECK_DIF_OK(dif_rstmgr_reset_info_get(&rstmgr, &rst_info));
  CHECK_DIF_OK(dif_rstmgr_reset_info_clear(&rstmgr));

  if (rst_info == kDifRstmgrResetInfoPor) {
    LOG_INFO("Booting for the first time, setting wdog");

    // Configure watchdog sooner then wakeup, but with pause enabled.
    CHECK(WKUP_TIME_US > WDOG_BITE_TIME_US);
    CHECK(WDOG_BARK_TIME_US < WDOG_BITE_TIME_US);
    uint32_t wkup_cycles =
        cycles_to_32_bits(us_to_aon_cycles(WKUP_TIME_US), "wkup_time");
    uint32_t bark_cycles =
        cycles_to_32_bits(us_to_aon_cycles(WDOG_BARK_TIME_US), "bark_time");
    uint32_t bite_cycles =
        cycles_to_32_bits(us_to_aon_cycles(WDOG_BITE_TIME_US), "bite_time");
    aon_timer_testutils_wakeup_config(&aon_timer, wkup_cycles);
    aon_timer_testutils_watchdog_config(&aon_timer, bark_cycles, bite_cycles,
                                        true);
    // Deep sleep.
    pwrmgr_testutils_enable_low_power(&pwrmgr,
                                      kDifPwrmgrWakeupRequestSourceFive,
                                      /*domain_config=*/0);

    // Enter low power mode.
    LOG_INFO("Issue WFI to enter sleep");
    wait_for_interrupt();
  } else if (rst_info == kDifRstmgrResetInfoLowPowerExit) {
    bool is_pending;
    LOG_INFO("Booting for the second time due to wakeup");
    // Executing the wdog bite reset during sleep test.

    // Wait for the remaining time to the wdog bark.
    usleep(WDOG_BARK_TIME_US);
    CHECK_DIF_OK(dif_aon_timer_irq_is_pending(
        &aon_timer, kDifAonTimerIrqWkupTimerExpired, &is_pending));
    CHECK(is_pending);

    CHECK_DIF_OK(dif_aon_timer_wakeup_stop(&aon_timer));

    CHECK_DIF_OK(dif_aon_timer_irq_acknowledge(
        &aon_timer, kDifAonTimerIrqWkupTimerExpired));
    usleep(WDOG_BITE_TIME_US - WDOG_BARK_TIME_US + 10);
    LOG_ERROR("Should have got a watchdog reset");
  } else if (rst_info == kDifRstmgrResetInfoWatchdog) {
    LOG_INFO("Booting for the third time due to wdog bite reset");
  } else {
    LOG_ERROR("Got unexpected reset_info=0x%x", rst_info);
  }

  return true;
}
