// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"

static const dt_pwrmgr_t kPwrmgrDt = 0;
static_assert(kDtPwrmgrCount == 1, "this test expects exactly one pwrmgr");
static const dt_aon_timer_t kAonTimerDt = 0;
static_assert(kDtAonTimerCount >= 1,
              "this test expects at least one aon_timer");

OTTF_DEFINE_TEST_CONFIG();

enum {
  kPattern = 0xab,
};

/**
 * Check that a region within the retention SRAM has not changed from kPattern.
 *
 * @param start A pointer to the start of the region to check.
 * @param length The number of 32-bit words to check.
 * @return Whether the region has changed.
 */
bool check_ram_region_unchanged(char *start, size_t length) {
  uint32_t pattern32;
  memset(&pattern32, kPattern, sizeof(pattern32));

  bool unchanged = true;
  for (size_t i = 0; i < length; i += sizeof(uint32_t)) {
    uint32_t val = read_32(start + i);
    if (val != pattern32) {
      LOG_ERROR("Retention SRAM changed at word %u (%x --> %x).",
                i / sizeof(uint32_t), pattern32, val);
      unchanged = false;
    }
  }
  return unchanged;
}

/**
 * Check that the values in the retention SRAM have not changed from kPattern.
 * Only the reserved sections of the silicon_owner and siilicon_creator
 * sections are checked as other entries may be updated during boot.
 */
bool check_ram_unchanged(retention_sram_t *ret) {
  LOG_INFO("Checking that retention SRAM values are unchanged");
  bool unchanged = true;
  const size_t creator_resv_size = sizeof(ret->creator.reserved);
  const size_t owner_resv_size = sizeof(ret->owner.reserved);
  // Ensure that the reserved section is sufficiently large for a robust check.
  // 1 word is an arbitrary limit, but if the reserved section is filled up, a
  // new testing approach will be needed.
  CHECK(creator_resv_size > sizeof(uint32_t));
  CHECK(owner_resv_size > sizeof(uint32_t));
  unchanged &= check_ram_region_unchanged((char *)&ret->creator.reserved,
                                          creator_resv_size);
  unchanged &=
      check_ram_region_unchanged((char *)&ret->owner.reserved, owner_resv_size);
  return unchanged;
}

rom_error_t retention_ram_keep_test(void) {
  // Variables of type `retention_sram_t` are static to reduce stack usage.
  retention_sram_t *ret = retention_sram_get();
  uint32_t reset_reasons = ret->creator.reset_reasons;

  // Verify that reset_reasons reports POR.
  if (bitfield_bit32_read(reset_reasons, kRstmgrReasonPowerOn)) {
    // This branch runs after the POR after initializing the testing environment

    LOG_INFO("Checking boot_log.retention_ram_initialized: %x",
             ret->creator.boot_log.retention_ram_initialized);
    CHECK(ret->creator.boot_log.retention_ram_initialized == kHardenedBoolTrue);
    LOG_INFO("Writing known pattern to ret RAM");
    memset(ret, kPattern, sizeof(retention_sram_t));

    // Initialize pwrmgr
    dif_pwrmgr_t pwrmgr;
    CHECK_DIF_OK(dif_pwrmgr_init_from_dt(kPwrmgrDt, &pwrmgr));
    dif_pwrmgr_request_sources_t wakeup_sources;
    CHECK_DIF_OK(dif_pwrmgr_find_request_source(
        &pwrmgr, kDifPwrmgrReqTypeWakeup, dt_aon_timer_instance_id(kAonTimerDt),
        kDtAonTimerWakeupWkupReq, &wakeup_sources));

    // Initialize aon timer
    // Issue a wakeup signal in ~150us through the AON timer.
    //
    // At 200kHz, threshold of 30 is equal to 150us. There is an additional
    // ~4 cycle overhead for the CSR value to synchronize with the AON clock.
    // We should expect the wake up to trigger in ~170us. This is sufficient
    // time to allow pwrmgr config and the low power entry on WFI to complete.
    //
    // Adjust the threshold for Verilator since it runs on different clock
    // frequencies.
    uint64_t wakeup_threshold = kDeviceType == kDeviceSimVerilator ? 300 : 30;

    dif_aon_timer_t aon_timer;
    CHECK_DIF_OK(dif_aon_timer_init_from_dt(kAonTimerDt, &aon_timer));
    CHECK_STATUS_OK(
        aon_timer_testutils_wakeup_config(&aon_timer, wakeup_threshold));

    // Enter low-power
    CHECK_STATUS_OK(
        pwrmgr_testutils_enable_low_power(&pwrmgr, wakeup_sources, 0));
    LOG_INFO("Issue WFI to enter sleep");
    wait_for_interrupt();  // Enter low-power
  } else if (bitfield_bit32_read(reset_reasons, kRstmgrReasonLowPowerExit)) {
    LOG_INFO("Woke up from low power exit");
    LOG_INFO("Checking boot_log.retention_ram_initialized: %x",
             ret->creator.boot_log.retention_ram_initialized);
    CHECK(ret->creator.boot_log.retention_ram_initialized ==
          kHardenedBoolFalse);
    CHECK(check_ram_unchanged(ret));

    // Request a SW reset
    LOG_INFO("Issuing a SW reset");
    rstmgr_reset();
  } else if (bitfield_bit32_read(reset_reasons, kRstmgrReasonSoftwareRequest)) {
    LOG_INFO("Resuming from SW reset");
    LOG_INFO("Checking boot_log.retention_ram_initialized: %x",
             ret->creator.boot_log.retention_ram_initialized);
    CHECK(ret->creator.boot_log.retention_ram_initialized ==
          kHardenedBoolFalse);
    // This branch runs after the SW-requested reset
    CHECK(check_ram_unchanged(ret));
    return kErrorOk;
  }
  LOG_ERROR("Did not find a reset reason of Low-Power Exit or SW request");
  return kErrorUnknown;
}

bool test_main(void) {
  status_t result = OK_STATUS();
  EXECUTE_TEST(result, retention_ram_keep_test);
  return status_ok(result);
}
