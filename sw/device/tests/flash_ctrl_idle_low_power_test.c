// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "dt/dt_adc_ctrl.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rand_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

OTTF_DEFINE_TEST_CONFIG();

static dif_rv_plic_t plic;
static dif_aon_timer_t aon;
static dif_rv_core_ibex_t rv_core_ibex;

enum {
  kPlicTarget = 0,
};

static const dt_adc_ctrl_t kAdcCtrlDt = 0;
static_assert(kDtAdcCtrlCount == 1, "this test expects a adc_ctrl");
static const dt_rstmgr_t kRstmgrDt = 0;
static_assert(kDtRstmgrCount == 1, "this test expects a rstmgr");
static const dt_pwrmgr_t kPwrmgrDt = 0;
static_assert(kDtPwrmgrCount == 1, "this test expects a pwrmgr");
static const dt_aon_timer_t kAonTimerDt = 0;
static_assert(kDtAonTimerCount == 1, "this test expects an aon_timer");
static const dt_rv_plic_t kRvPlicDt = 0;
static_assert(kDtRvPlicCount == 1, "this test expects exactly one rv_plic");
static const dt_rv_core_ibex_t kRvCoreIbexDt = 0;
static_assert(kDtRvCoreIbexCount == 1,
              "this test expects exactly one rv_core_ibex");
static const dt_flash_ctrl_t kFlashCtrlDt = 0;
static_assert(kDtFlashCtrlCount >= 1,
              "this test expects at least one flash_ctrl");

static volatile bool irq_serviced = false;

enum {
  kFlashDataRegion = 0,
  kRegionBasePageIndex = 256,  // First page in bank 1 (avoids program code.)
  kPartitionId = 0,
  kRegionSize = 1,
  kNumWords = 128,
  kAONBarkTh = 64,
  kAONBiteTh = 256,
};

/**
 * External interrupt handler.
 */
bool ottf_handle_irq(uint32_t *exc_info, dt_instance_id_t devid,
                     dif_rv_plic_irq_id_t irq_id) {
  if (devid == dt_aon_timer_instance_id(kAonTimerDt) &&
      irq_id == dt_aon_timer_irq_to_plic_id(kAonTimerDt,
                                            kDtAonTimerIrqWdogTimerBark)) {
    CHECK_DIF_OK(
        dif_aon_timer_irq_acknowledge(&aon, kDtAonTimerIrqWdogTimerBark));
    irq_serviced = true;
    return true;
  } else {
    return false;
  }
}

/**
 * OTTF external NMI internal IRQ handler.
 * The ROM configures the watchdog to generates a NMI at bark, so we clean the
 * NMI and wait the external irq handler next.
 */
void ottf_external_nmi_handler(void) {
  bool is_pending;
  // The watchdog bark external interrupt is also connected to the NMI input
  // of rv_core_ibex. We therefore expect the interrupt to be pending on the
  // peripheral side (the check is done later in the test function).
  CHECK_DIF_OK(dif_aon_timer_irq_is_pending(&aon, kDifAonTimerIrqWdogTimerBark,
                                            &is_pending));
  // In order to handle the NMI we need to acknowledge the interrupt status
  // bit it at the peripheral side.
  CHECK_DIF_OK(
      dif_aon_timer_irq_acknowledge(&aon, kDifAonTimerIrqWdogTimerBark));

  CHECK_DIF_OK(dif_rv_core_ibex_clear_nmi_state(&rv_core_ibex,
                                                kDifRvCoreIbexNmiSourceAll));
}

static void enable_irqs(void) {
  // Enable the AON bark interrupt.
  dif_rv_plic_irq_id_t plic_id =
      dt_aon_timer_irq_to_plic_id(kAonTimerDt, kDtAonTimerIrqWdogTimerBark);
  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(&plic, plic_id, kPlicTarget,
                                           kDifToggleEnabled));
  CHECK_DIF_OK(
      dif_rv_plic_irq_set_priority(&plic, plic_id, kDifRvPlicMaxPriority));
  CHECK_DIF_OK(dif_rv_plic_target_set_threshold(&plic, kPlicTarget, 0x0));
  // Enable the external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);
}

bool test_main(void) {
  dif_flash_ctrl_state_t flash;
  dif_pwrmgr_t pwrmgr;
  dif_rstmgr_t rstmgr;

  CHECK_DIF_OK(dif_rv_plic_init_from_dt(kRvPlicDt, &plic));
  CHECK_DIF_OK(dif_flash_ctrl_init_state_from_dt(&flash, kFlashCtrlDt));
  CHECK_DIF_OK(dif_pwrmgr_init_from_dt(kPwrmgrDt, &pwrmgr));
  CHECK_DIF_OK(dif_rstmgr_init_from_dt(kRstmgrDt, &rstmgr));
  CHECK_DIF_OK(dif_aon_timer_init_from_dt(kAonTimerDt, &aon));
  CHECK_DIF_OK(dif_rv_core_ibex_init_from_dt(kRvCoreIbexDt, &rv_core_ibex));
  enable_irqs();

  dif_pwrmgr_request_sources_t wakeup_sources;
  CHECK_DIF_OK(dif_pwrmgr_find_request_source(
      &pwrmgr, kDifPwrmgrReqTypeWakeup, dt_adc_ctrl_instance_id(kAdcCtrlDt),
      kDtAdcCtrlWakeupWkupReq, &wakeup_sources));

  dif_pwrmgr_request_sources_t reset_sources;
  CHECK_DIF_OK(dif_pwrmgr_find_request_source(
      &pwrmgr, kDifPwrmgrReqTypeReset, dt_aon_timer_instance_id(kAonTimerDt),
      kDtAonTimerResetReqAonTimer, &reset_sources));

  CHECK_DIF_OK(dif_aon_timer_watchdog_stop(&aon));
  CHECK_DIF_OK(dif_pwrmgr_set_request_sources(
      &pwrmgr, kDifPwrmgrReqTypeReset, reset_sources, kDifToggleEnabled));

  dif_rstmgr_reset_info_bitfield_t rstmgr_reset_info;
  rstmgr_reset_info = rstmgr_testutils_reason_get();

  uint32_t address = 0;
  CHECK_STATUS_OK(flash_ctrl_testutils_data_region_setup(
      &flash, kRegionBasePageIndex, kFlashDataRegion, kRegionSize, &address));

  if (rstmgr_reset_info == kDifRstmgrResetInfoPor) {
    // Create data. Random data will be different than
    // the 0xFFFFFFFF that is created with an erase.
    uint32_t data[kNumWords];
    for (int i = 0; i < kNumWords; ++i) {
      data[i] = rand_testutils_gen32();
    }

    // Erasing the page and writing data to it followed
    // by a read back and compare to sanity check basic operation.
    CHECK_STATUS_OK(flash_ctrl_testutils_erase_and_write_page(
        &flash, address, kPartitionId, data, kDifFlashCtrlPartitionTypeData,
        kNumWords));
    uint32_t readback_data[kNumWords];
    CHECK_STATUS_OK(flash_ctrl_testutils_read(
        &flash, address, kPartitionId, readback_data,
        kDifFlashCtrlPartitionTypeData, kNumWords, 0));
    CHECK_ARRAYS_EQ(data, readback_data, kNumWords);

    // Setting up low power hint and starting watchdog timer followed by
    // a flash operation (page erase) and WFI. This will create a bark
    // interrupt at some time following the start of the flash operation.
    CHECK_STATUS_OK(
        pwrmgr_testutils_enable_low_power(&pwrmgr, wakeup_sources, 0));

    CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_clear(&pwrmgr));

    CHECK_DIF_OK(dif_aon_timer_watchdog_stop(&aon));

    uint32_t bark_th = kAONBarkTh;
    uint32_t bite_th = kAONBiteTh;

    // Update bark and bite threshold in case of silicon test
    if (kDeviceType == kDeviceSilicon) {
      bark_th = 4000;
      bite_th = 4 * bark_th;
    }
    CHECK_DIF_OK(dif_aon_timer_watchdog_start(
        &aon /* aon */, bark_th /* bark_threshold */,
        bite_th /* bite_threshold */, false /* pause_in_sleep */,
        false /* lock */));

    dif_flash_ctrl_transaction_t transaction = {
        .byte_address = address,
        .op = kDifFlashCtrlOpPageErase,
        .partition_type = kDifFlashCtrlPartitionTypeData,
        .partition_id = kPartitionId,
        .word_count = 0x0};

    CHECK_DIF_OK(dif_flash_ctrl_start(&flash, transaction));
    // Do not put any print here.
    // That will cause interrupt miss and spurious test failure
    wait_for_interrupt();

    // Return from interrupt. Stop the watchdog. Check the reset info
    // is still POR and the interrupt came from the correct source.
    // Check the erase operation completed successfully.
    CHECK_DIF_OK(dif_aon_timer_watchdog_stop(&aon));

    dif_pwrmgr_wakeup_reason_t reason;
    CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_get(&pwrmgr, &reason));
    CHECK(reason.types == kDifPwrmgrWakeupTypeAbort,
          "Unexpected wakeup reason: types=%x, srcs=%x", reason.types,
          reason.request_sources);

    CHECK(irq_serviced);

    CHECK_STATUS_OK(flash_ctrl_testutils_wait_transaction_end(&flash));

    CHECK_STATUS_OK(flash_ctrl_testutils_read(
        &flash, address, kPartitionId, readback_data,
        kDifFlashCtrlPartitionTypeData, kNumWords, 0));
    uint32_t expected_data[kNumWords];
    memset(expected_data, 0xff, sizeof(expected_data));
    CHECK_ARRAYS_EQ(readback_data, expected_data, kNumWords);

    rstmgr_testutils_reason_clear();
  } else {
    LOG_ERROR("Unexepected reset type detected. Reset info = %08x",
              rstmgr_reset_info);
    return false;
  }

  return true;
}
