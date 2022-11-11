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
#include "sw/device/lib/testing/sram_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

enum {
  /**
   * Retention SRAM start address (inclusive).
   */
  kRetSramBaseAddr = TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR,

  kRetSramOwnerAddr =
      kRetSramBaseAddr + offsetof(retention_sram_t, reserved_owner),
  kRetRamLastAddr =
      kRetSramBaseAddr + TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_SIZE_BYTES - 1,

  kTestBufferSizeWords = 16,
};

OTTF_DEFINE_TEST_CONFIG();

// Random data to read/write to/from retention SRAM.
const uint32_t kTestData[kTestBufferSizeWords] = {
    0xe647e5d5, 0x4b5fe6f6, 0x1608a98a, 0x5e347116, 0xb2dc5e92, 0x899e3c0f,
    0xc98295c2, 0x0fa84434, 0x15747561, 0xfecb5aa1, 0x7a78bb8c, 0x8f9c5d0f,
    0x49338fbd, 0x093e82cb, 0xaaa58121, 0x5b806f96,
};

typedef struct {
  bool do_write;
  bool is_equal;
} check_config_t;

static void retention_sram_check(check_config_t config) {
  if (config.do_write) {
    sram_ctrl_testutils_write(
        kRetSramOwnerAddr,
        (sram_ctrl_testutils_data_t){.words = kTestData,
                                     .len = kTestBufferSizeWords});
  }

  uint32_t tmp_buffer[kTestBufferSizeWords];
  memcpy(tmp_buffer, (uint8_t *)kRetSramOwnerAddr, sizeof(tmp_buffer));

  if (config.is_equal) {
    CHECK_ARRAYS_EQ(tmp_buffer, kTestData, kTestBufferSizeWords);
  } else {
    CHECK_ARRAYS_NE(tmp_buffer, kTestData, kTestBufferSizeWords);
  }
}

/**
 * Override internal IRQ interrupt service routine to count
 * the number of integrity exceptions.
 */
void ottf_internal_isr(void) {}

bool test_main(void) {
  dif_pwrmgr_t pwrmgr;
  dif_rstmgr_t rstmgr;
  dif_aon_timer_t aon_timer;
  dif_sram_ctrl_t ret_sram;

  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));
  CHECK_DIF_OK(dif_aon_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR), &aon_timer));

  CHECK_DIF_OK(dif_sram_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_BASE_ADDR),
      &ret_sram));

  dif_rstmgr_reset_info_bitfield_t rstmgr_reset_info;
  rstmgr_reset_info = rstmgr_testutils_reason_get();

  LOG_INFO("Reset info = %08x", rstmgr_reset_info);

  if (rstmgr_reset_info == kDifRstmgrResetInfoPor) {
    LOG_INFO("POR reset");

    LOG_INFO("Scrambling...");
    sram_ctrl_testutils_scramble(&ret_sram);

    // Write data to retention SRAM and readback (to test basic functionality.)
    retention_sram_check((check_config_t){.do_write = true, .is_equal = true});

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
      retention_sram_check(
          (check_config_t){.do_write = false, .is_equal = true});

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

      // Enter low power mode.
      LOG_INFO("Issue WFI to enter sleep");
      aon_timer_testutils_watchdog_config(&aon_timer, UINT32_MAX, 20, false);
      wait_for_interrupt();
    } else {
      LOG_INFO("Watchdog reset");
      // Check that the previously written retention SRAM data cannot be read
      // successfully.
      retention_sram_check(
          (check_config_t){.do_write = false, .is_equal = false});
    }
  } else {
    LOG_FATAL("Unexepected reset type detected.");
  }

  // Turn off the AON timer hardware completely before exiting.
  aon_timer_testutils_shutdown(&aon_timer);
  CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));
  return true;
}
