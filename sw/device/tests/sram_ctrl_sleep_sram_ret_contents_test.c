// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define NUM_TEST_WORDS 16

OTTF_DEFINE_TEST_CONFIG();

// Random data to read/write to/from retention SRAM.
const uint32_t kTestData[NUM_TEST_WORDS] = {
    0xe647e5d5, 0x4b5fe6f6, 0x1608a98a, 0x5e347116, 0xb2dc5e92, 0x899e3c0f,
    0xc98295c2, 0x0fa84434, 0x15747561, 0xfecb5aa1, 0x7a78bb8c, 0x8f9c5d0f,
    0x49338fbd, 0x093e82cb, 0xaaa58121, 0x5b806f96,
};

static void retention_sram_check(bool do_write) {
  mmio_region_t sram_region_ret_base_addr =
      mmio_region_from_addr(TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR);
  for (int i = 0; i < NUM_TEST_WORDS * sizeof(uint32_t);
       i += sizeof(uint32_t)) {
    // Don't write or check reset_reasons because this test uses them to reboot
    if (i != offsetof(struct retention_sram, reset_reasons)) {
      if (do_write) {
        mmio_region_write32(sram_region_ret_base_addr, i, kTestData[i]);
      }
      uint32_t read_data = mmio_region_read32(sram_region_ret_base_addr, i);
      CHECK(read_data == kTestData[i]);
    }
  }
}

bool test_main(void) {
  dif_pwrmgr_t pwrmgr;
  dif_rstmgr_t rstmgr;
  dif_aon_timer_t aon_timer;

  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));
  CHECK_DIF_OK(dif_aon_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR), &aon_timer));

  dif_rstmgr_reset_info_bitfield_t rstmgr_reset_info;
  rstmgr_reset_info = rstmgr_testutils_reason_get();

  LOG_INFO("Reset info = %08x", rstmgr_reset_info);

  if (rstmgr_reset_info == kDifRstmgrResetInfoPor) {
    LOG_INFO("POR reset");

    // Write data to retention SRAM and readback (to test basic functionality.)
    retention_sram_check(true);

    // Prepare rstmgr for a reset.
    rstmgr_testutils_pre_reset(&rstmgr);
    aon_timer_testutils_wakeup_config(&aon_timer, 20);
    // Deep sleep.
    pwrmgr_testutils_enable_low_power(&pwrmgr,
                                      kDifPwrmgrWakeupRequestSourceFive, 0);

    // Enter low power mode.
    LOG_INFO("Issue WFI to enter sleep");
    wait_for_interrupt();
  } else if (rstmgr_reset_info & kDifRstmgrResetInfoLowPowerExit) {
    if (!(rstmgr_reset_info & kDifRstmgrResetInfoWatchdog)) {
      LOG_INFO("Wakeup reset");

      CHECK(pwrmgr_testutils_is_wakeup_reason(
          &pwrmgr, kDifPwrmgrWakeupRequestSourceFive));

      LOG_INFO("Aon timer wakeup detected");

      // Check that the previously written retention SRAM data can still
      // be read successfully.
      retention_sram_check(false);

      // Prepare rstmgr for a reset.
      rstmgr_testutils_pre_reset(&rstmgr);
      // Deep sleep.
      pwrmgr_testutils_enable_low_power(&pwrmgr,
                                        kDifPwrmgrWakeupRequestSourceTwo, 0);
      // Enable watchdog timer.
      CHECK_DIF_OK(dif_pwrmgr_set_request_sources(
          &pwrmgr, kDifPwrmgrReqTypeReset, kDifPwrmgrResetRequestSourceTwo,
          kDifToggleEnabled));

      CHECK_DIF_OK(dif_aon_timer_wakeup_stop(&aon_timer));
      aon_timer_testutils_watchdog_config(&aon_timer, 0xffffffff, 10, false);

      // Enter low power mode.
      LOG_INFO("Issue WFI to enter sleep");
      wait_for_interrupt();
    } else {
      LOG_INFO("Watchdog reset");
      // Check that the previously written retention SRAM data can still
      // be read successfully.
      retention_sram_check(false);
    }
  } else {
    LOG_FATAL("Unexepected reset type detected.");
  }

  return true;
}
