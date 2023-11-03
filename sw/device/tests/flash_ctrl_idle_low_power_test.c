// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

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

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "sw/device/lib/testing/autogen/isr_testutils.h"

OTTF_DEFINE_TEST_CONFIG();

static dif_rv_plic_t plic;
static dif_aon_timer_t aon;

static plic_isr_ctx_t plic_ctx = {
    .rv_plic = &plic,
    .hart_id = kTopEarlgreyPlicTargetIbex0,
};

static aon_timer_isr_ctx_t aon_timer_ctx = {
    .aon_timer = &aon,
    .plic_aon_timer_start_irq_id =
        kTopEarlgreyPlicIrqIdAonTimerAonWkupTimerExpired,
    .is_only_irq = false,
};

static top_earlgrey_plic_peripheral_t peripheral_serviced;
static dif_aon_timer_irq_t irq_serviced;

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
void ottf_external_isr(void) {
  isr_testutils_aon_timer_isr(plic_ctx, aon_timer_ctx, &peripheral_serviced,
                              &irq_serviced);
}

static void enable_irqs(void) {
  // Enable the AON bark interrupt.
  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(
      &plic, kTopEarlgreyPlicIrqIdAonTimerAonWdogTimerBark,
      kTopEarlgreyPlicTargetIbex0, kDifToggleEnabled));
  CHECK_DIF_OK(dif_rv_plic_irq_set_priority(
      &plic, kTopEarlgreyPlicIrqIdAonTimerAonWdogTimerBark,
      kDifRvPlicMaxPriority));
  CHECK_DIF_OK(dif_rv_plic_target_set_threshold(
      &plic, kTopEarlgreyPlicTargetIbex0, 0x0));
  // Enable the external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);
}

bool test_main(void) {
  dif_flash_ctrl_state_t flash;
  dif_pwrmgr_t pwrmgr;
  dif_rstmgr_t rstmgr;

  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &plic));
  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash, mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));
  CHECK_DIF_OK(dif_aon_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR), &aon));

  enable_irqs();

  CHECK_DIF_OK(dif_aon_timer_watchdog_stop(&aon));
  CHECK_DIF_OK(dif_pwrmgr_set_request_sources(&pwrmgr, kDifPwrmgrReqTypeReset,
                                              kDifPwrmgrResetRequestSourceTwo,
                                              kDifToggleEnabled));

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
    // a flash operation (page erase) and WFI. This will create a bite
    // interrupt at some time following the start of the flash operation.
    CHECK_STATUS_OK(pwrmgr_testutils_enable_low_power(
        &pwrmgr, kDifPwrmgrWakeupRequestSourceTwo, 0));

    CHECK_DIF_OK(dif_aon_timer_watchdog_stop(&aon));
    CHECK_DIF_OK(dif_aon_timer_watchdog_start(
        &aon /* aon */, kAONBarkTh /* bark_threshold */,
        kAONBiteTh /* bite_threshold */, false /* pause_in_sleep */,
        false /* lock */));

    dif_flash_ctrl_transaction_t transaction = {
        .byte_address = address,
        .op = kDifFlashCtrlOpPageErase,
        .partition_type = kDifFlashCtrlPartitionTypeData,
        .partition_id = kPartitionId,
        .word_count = 0x0};

    CHECK_DIF_OK(dif_flash_ctrl_start(&flash, transaction));
    wait_for_interrupt();

    // Return from interrupt. Stop the watchdog. Check the reset info
    // is still POR and the interrupt came from the correct source.
    // Check the erase operation completed successfully.
    CHECK_DIF_OK(dif_aon_timer_watchdog_stop(&aon));

    rstmgr_reset_info = rstmgr_testutils_reason_get();
    CHECK(rstmgr_reset_info == kDifRstmgrResetInfoPor);
    CHECK(peripheral_serviced == kTopEarlgreyPlicPeripheralAonTimerAon);
    CHECK(irq_serviced == kDifAonTimerIrqWdogTimerBark);

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
