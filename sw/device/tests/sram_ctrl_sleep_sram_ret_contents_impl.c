// Copyright lowRISC contributors (OpenTitan project).
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
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"

enum {
  kTestBufferSizeWords = 16,
  kPlicTarget = 0,
};

static dif_rv_plic_t rv_plic;
static dif_aon_timer_t aon_timer;
static dif_pwrmgr_t pwrmgr;
static dif_rstmgr_t rstmgr;

static const dt_rstmgr_t kRstmgrDt = 0;
static_assert(kDtRstmgrCount == 1, "this test expects a rstmgr");
static const dt_pwrmgr_t kPwrmgrDt = 0;
static_assert(kDtPwrmgrCount == 1, "this library expects exactly one pwrmgr");
static const dt_aon_timer_t kAonTimerDt = 0;
static_assert(kDtAonTimerCount == 1,
              "this library expects exactly one aon_timer");
static const dt_rv_plic_t kRvPlicDt = 0;
static_assert(kDtRvPlicCount >= 1, "this test expects at least one rv_plic");

static const dt_sram_ctrl_t kRetSramCtrlDt = kDtSramCtrlRetAon;

static dif_pwrmgr_request_sources_t aon_timer_wakeup_sources;

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
  uintptr_t ret_sram_owner_addr =
      dt_sram_ctrl_reg_block(kRetSramCtrlDt, kDtSramCtrlRegBlockRam) +
      offsetof(retention_sram_t, owner);

  if (config.do_write) {
    sram_ctrl_testutils_write(
        ret_sram_owner_addr,
        (sram_ctrl_testutils_data_t){.words = kTestData,
                                     .len = kTestBufferSizeWords});
  }

  uint32_t tmp_buffer[kTestBufferSizeWords];
  memcpy(tmp_buffer, (uint8_t *)ret_sram_owner_addr, sizeof(tmp_buffer));

  if (config.is_equal) {
    CHECK_ARRAYS_EQ(tmp_buffer, kTestData, kTestBufferSizeWords);
  } else {
    CHECK_ARRAYS_NE(tmp_buffer, kTestData, kTestBufferSizeWords);
  }
  LOG_INFO("retention ram check with write=%d and is_equal=%d succeeded",
           config.do_write, config.is_equal);
}

/**
 * Override internal interrupt handler to handle the ECC errors when reading the
 * scrambled memory.
 */
void ottf_internal_isr(uint32_t *exc_info) {}

/**
 * Override external interrupt handler to handle the normal sleep IRQ.
 */
bool ottf_handle_irq(uint32_t *exc_info, dt_instance_id_t devid,
                     dif_rv_plic_irq_id_t irq_id) {
  if (devid == dt_pwrmgr_instance_id(kPwrmgrDt) &&
      irq_id == dt_pwrmgr_irq_to_plic_id(kPwrmgrDt, kDtPwrmgrIrqWakeup)) {
    LOG_INFO("Receive irq in normal sleep");
    CHECK_DIF_OK(dif_pwrmgr_irq_acknowledge(&pwrmgr, kDtPwrmgrIrqWakeup));
    return true;
  } else {
    return false;
  }
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
  dif_rv_plic_irq_id_t irq_id =
      dt_pwrmgr_irq_to_plic_id(kPwrmgrDt, kDtPwrmgrIrqWakeup);
  rv_plic_testutils_irq_range_enable(&rv_plic, kPlicTarget, irq_id, irq_id);
  CHECK_DIF_OK(dif_pwrmgr_irq_set_enabled(&pwrmgr, 0, kDifToggleEnabled));

  // Normal sleep.
  CHECK_STATUS_OK(pwrmgr_testutils_enable_low_power(
      &pwrmgr, /*wakeups=*/aon_timer_wakeup_sources,
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
  CHECK_STATUS_OK(
      pwrmgr_testutils_enable_low_power(&pwrmgr, aon_timer_wakeup_sources, 0));

  // Enter low power mode.
  LOG_INFO("Issue WFI to enter deep sleep");
  wait_for_interrupt();
  CHECK(false, "Should have a reset to CPU before this line");
}

void set_up_reset_request(void) {
  // Prepare rstmgr for a reset.
  CHECK_STATUS_OK(rstmgr_testutils_pre_reset(&rstmgr));
  dif_pwrmgr_request_sources_t reset_sources;
  CHECK_DIF_OK(dif_pwrmgr_find_request_source(
      &pwrmgr, kDifPwrmgrReqTypeReset, dt_aon_timer_instance_id(kAonTimerDt),
      kDtAonTimerResetReqAonTimer, &reset_sources));
  CHECK_DIF_OK(dif_pwrmgr_set_request_sources(
      &pwrmgr, kDifPwrmgrReqTypeReset, reset_sources, kDifToggleEnabled));

  CHECK_DIF_OK(dif_aon_timer_wakeup_stop(&aon_timer));

  // Enter low power mode. Use UINT32_MAX as wakeup threshold as UINT64_MAX far
  // too long a timeout.
  CHECK_STATUS_OK(aon_timer_testutils_watchdog_config(
      &aon_timer, (uint64_t)UINT32_MAX, 20, false));
  LOG_INFO("wait for reset");
  wait_for_interrupt();
  CHECK(false, "Should have a reset to CPU and ret_sram before this line");
}

bool execute_sram_ctrl_sleep_ret_sram_contents_test(bool scramble) {
  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  CHECK_DIF_OK(dif_pwrmgr_init_from_dt(kPwrmgrDt, &pwrmgr));
  CHECK_DIF_OK(dif_rstmgr_init_from_dt(kRstmgrDt, &rstmgr));
  CHECK_DIF_OK(dif_aon_timer_init_from_dt(kAonTimerDt, &aon_timer));
  CHECK_DIF_OK(dif_rv_plic_init_from_dt(kRvPlicDt, &rv_plic));

  CHECK_DIF_OK(dif_pwrmgr_find_request_source(
      &pwrmgr, kDifPwrmgrReqTypeWakeup, dt_aon_timer_instance_id(kAonTimerDt),
      kDtAonTimerWakeupWkupReq, &aon_timer_wakeup_sources));

  dif_rstmgr_reset_info_bitfield_t rstmgr_reset_info;
  rstmgr_reset_info = rstmgr_testutils_reason_get();

  LOG_INFO("Reset info = %08x", rstmgr_reset_info);

  if (rstmgr_reset_info == kDifRstmgrResetInfoPor) {
    LOG_INFO("POR reset");
    LOG_INFO("Start to test retention sram %sscrambled",
             scramble ? "" : "not ");

    if (scramble) {
      dif_sram_ctrl_t ret_sram;
      CHECK_DIF_OK(dif_sram_ctrl_init_from_dt(kRetSramCtrlDt, &ret_sram));
      LOG_INFO("Wiping ret_sram...");
      CHECK_STATUS_OK(sram_ctrl_testutils_wipe(&ret_sram));
      LOG_INFO("Scrambling ret_sram...");
      CHECK_STATUS_OK(sram_ctrl_testutils_scramble(&ret_sram));
    }
    test_ret_sram_in_normal_sleep();

    enter_deep_sleep();
  } else if (rstmgr_reset_info & kDifRstmgrResetInfoLowPowerExit) {
    LOG_INFO("Wake up from deep sleep");

    CHECK(UNWRAP(pwrmgr_testutils_is_wakeup_reason(
              &pwrmgr, aon_timer_wakeup_sources)) == true);
    // data preserved
    retention_sram_check((check_config_t){.do_write = false, .is_equal = true});

    set_up_reset_request();
  } else if (rstmgr_reset_info & kDifRstmgrResetInfoWatchdog) {
    LOG_INFO("watchdog reset");
    // reset due to a reset request, if scramble data is not preserved.
    retention_sram_check(
        (check_config_t){.do_write = false, .is_equal = !scramble});
  } else {
    LOG_FATAL("Unexepected reset type detected.");
    return false;
  }

  return true;
}
