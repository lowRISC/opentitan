// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/sram_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "sw/device/lib/testing/autogen/isr_testutils.h"

enum {
  /**
   * Retention SRAM start address (inclusive).
   */
  kRetSramBaseAddr = TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR,

  kRetSramOwnerAddr = kRetSramBaseAddr + offsetof(retention_sram_t, owner),
  kRetRamLastAddr =
      kRetSramBaseAddr + TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_SIZE_BYTES - 1,

  kTestBufferSizeWords = 16,
};

OTTF_DEFINE_TEST_CONFIG();

static dif_rv_plic_t rv_plic;
static dif_aon_timer_t aon_timer;
static dif_pwrmgr_t pwrmgr;
static dif_rstmgr_t rstmgr;
static plic_isr_ctx_t plic_ctx = {.rv_plic = &rv_plic,
                                  .hart_id = kTopEarlgreyPlicTargetIbex0};
static pwrmgr_isr_ctx_t pwrmgr_isr_ctx = {
    .pwrmgr = &pwrmgr,
    .plic_pwrmgr_start_irq_id = kTopEarlgreyPlicIrqIdPwrmgrAonWakeup,
    .expected_irq = kDifPwrmgrIrqWakeup,
    .is_only_irq = true};

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

// this is preserved across resets. Flash default value is all 1s,
// can be written to 0 without an erase, so name this `non` scramble.
// flash doesn't support byte write, hence define it to a 32 bit int.
OT_SET_BSS_SECTION(".non_volatile_scratch", uint32_t ret_non_scrambled;)

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
 * Override internal interrupt handler to handle the ECC errors when reading the
 * scrambled memory.
 */
void ottf_internal_isr(void) {}

/**
 * Override external interrupt handler to handle the normal sleep IRQ.
 */
void ottf_external_isr(void) {
  dif_pwrmgr_irq_t irq_id;
  top_earlgrey_plic_peripheral_t peripheral;

  isr_testutils_pwrmgr_isr(plic_ctx, pwrmgr_isr_ctx, &peripheral, &irq_id);

  LOG_INFO("Receive irq in normal sleep");
  // Check that both the peripheral and the irq id are correct.
  CHECK(peripheral == kTopEarlgreyPlicPeripheralPwrmgrAon,
        "IRQ peripheral: %d is incorrect", peripheral);
  CHECK(irq_id == kDifPwrmgrIrqWakeup, "IRQ ID: %d is incorrect", irq_id);
}

// test these 2 cases:
// normal sleep, no scrambling -> data preserved
// normal sleep, with scrambling -> data preserved
void test_ret_sram_in_normal_sleep(void) {
  // Write data to retention SRAM and readback (to test basic functionality.)
  retention_sram_check((check_config_t){.do_write = true, .is_equal = true});

  // set up wakeup timer
  CHECK_STATUS_OK(aon_timer_testutils_wakeup_config(&aon_timer, 20));
  // Enable all the AON interrupts used in this test.
  rv_plic_testutils_irq_range_enable(&rv_plic, kTopEarlgreyPlicTargetIbex0,
                                     kTopEarlgreyPlicIrqIdPwrmgrAonWakeup,
                                     kTopEarlgreyPlicIrqIdPwrmgrAonWakeup);
  CHECK_DIF_OK(dif_pwrmgr_irq_set_enabled(&pwrmgr, 0, kDifToggleEnabled));

  // Normal sleep.
  CHECK_STATUS_OK(pwrmgr_testutils_enable_low_power(
      &pwrmgr, /*wakeups=*/kDifPwrmgrWakeupRequestSourceFive,
      /*domain_config=*/kDifPwrmgrDomainOptionCoreClockInLowPower |
          kDifPwrmgrDomainOptionUsbClockInActivePower |
          kDifPwrmgrDomainOptionMainPowerInLowPower));
  // Enter low power mode.
  LOG_INFO("Issue WFI to enter normal sleep");
  wait_for_interrupt();
  // data preserved
  retention_sram_check((check_config_t){.do_write = false, .is_equal = true});
}

// test these 2 cases:
// deep sleep, no scrambling -> data preserved
// deep sleep, with scrambling -> data preserved
void enter_deep_sleep(void) {
  // Prepare rstmgr for a reset.
  CHECK_STATUS_OK(rstmgr_testutils_pre_reset(&rstmgr));
  // set up wakeup timer
  CHECK_STATUS_OK(aon_timer_testutils_wakeup_config(&aon_timer, 20));
  // Deep sleep.
  CHECK_STATUS_OK(pwrmgr_testutils_enable_low_power(
      &pwrmgr, kDifPwrmgrWakeupRequestSourceFive, 0));

  // Enter low power mode.
  LOG_INFO("Issue WFI to enter deep sleep");
  wait_for_interrupt();
  CHECK(false, "Should have a reset to CPU before this line");
}

void set_up_reset_request(void) {
  // Prepare rstmgr for a reset.
  CHECK_STATUS_OK(rstmgr_testutils_pre_reset(&rstmgr));
  CHECK_DIF_OK(dif_pwrmgr_set_request_sources(&pwrmgr, kDifPwrmgrReqTypeReset,
                                              kDifPwrmgrResetRequestSourceTwo,
                                              kDifToggleEnabled));

  CHECK_DIF_OK(dif_aon_timer_wakeup_stop(&aon_timer));

  // Enter low power mode.
  CHECK_STATUS_OK(
      aon_timer_testutils_watchdog_config(&aon_timer, UINT32_MAX, 20, false));
  LOG_INFO("wait for reset");
  wait_for_interrupt();
  CHECK(false, "Should have a reset to CPU and ret_sram before this line");
}

bool test_main(void) {
  dif_sram_ctrl_t ret_sram;

  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  mmio_region_t addr = mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_pwrmgr_init(addr, &pwrmgr));
  addr = mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_rstmgr_init(addr, &rstmgr));
  addr = mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_aon_timer_init(addr, &aon_timer));
  addr = mmio_region_from_addr(TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_BASE_ADDR);
  CHECK_DIF_OK(dif_sram_ctrl_init(addr, &ret_sram));
  addr = mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_plic_init(addr, &rv_plic));

  dif_rstmgr_reset_info_bitfield_t rstmgr_reset_info;
  rstmgr_reset_info = rstmgr_testutils_reason_get();

  LOG_INFO("Reset info = %08x", rstmgr_reset_info);

  if (rstmgr_reset_info == kDifRstmgrResetInfoPor) {
    LOG_INFO("POR reset");

    test_ret_sram_in_normal_sleep();

    enter_deep_sleep();
  } else if (rstmgr_reset_info & kDifRstmgrResetInfoLowPowerExit) {
    // This branch will be entered twice.
    // In the first time, ret_non_scrambled is True. In the 2nd time, it's
    // false.
    LOG_INFO("wake up from deep sleep with ret_non_scrambled: %x",
             ret_non_scrambled);

    CHECK(UNWRAP(pwrmgr_testutils_is_wakeup_reason(
              &pwrmgr, kDifPwrmgrWakeupRequestSourceFive)) == true);
    // data preserved
    retention_sram_check((check_config_t){.do_write = false, .is_equal = true});

    set_up_reset_request();
  } else if (rstmgr_reset_info & kDifRstmgrResetInfoWatchdog) {
    // This branch will be entered twice.
    // In the first time, ret_non_scrambled is True. In the 2nd time, it's
    // false.
    LOG_INFO("watchdog reset with ret_non_scrambled: %x", ret_non_scrambled);
    if (ret_non_scrambled) {
      // reset due to a reset request, no scrambling -> data preserved
      retention_sram_check(
          (check_config_t){.do_write = false, .is_equal = true});

      LOG_INFO("Start to test ret_sram with scramble enabled");

      dif_flash_ctrl_state_t flash_ctrl_state;
      CHECK_DIF_OK(dif_flash_ctrl_init_state(
          &flash_ctrl_state,
          mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
      CHECK_STATUS_OK(
          flash_ctrl_testutils_default_region_access(&flash_ctrl_state,
                                                     /*rd_en=*/true,
                                                     /*prog_en=*/true,
                                                     /*erase_en=*/true,
                                                     /*scramble_en=*/false,
                                                     /*ecc_en=*/false,
                                                     /*he_en=*/false));
      // write ret_non_scrambled to 0
      const uint32_t new_data = 0;
      CHECK_STATUS_OK(flash_ctrl_testutils_write(
          &flash_ctrl_state,
          (uint32_t)&ret_non_scrambled - TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR,
          /*partition_id=*/0, &new_data, kDifFlashCtrlPartitionTypeData,
          /*word_count=*/1));
      // wipe data otherwise, the data may still be read after reset, since it's
      // written with the default key/nounce.
      LOG_INFO("Wiping ret_sram...");
      CHECK_STATUS_OK(sram_ctrl_testutils_wipe(&ret_sram));
      LOG_INFO("Scrambling ret_sram...");
      CHECK_STATUS_OK(sram_ctrl_testutils_scramble(&ret_sram));

      test_ret_sram_in_normal_sleep();

      enter_deep_sleep();
    } else {
      // reset due to a reset request, with scrambling -> data NOT preserved
      retention_sram_check(
          (check_config_t){.do_write = false, .is_equal = false});
    }
  } else {
    LOG_FATAL("Unexepected reset type detected.");
  }

  return true;
}
