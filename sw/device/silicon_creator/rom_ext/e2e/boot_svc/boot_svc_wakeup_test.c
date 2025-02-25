// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_empty.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/rom_ext/e2e/boot_svc/boot_svc_test_lib.h"

static const dt_pwrmgr_t kPwrmgrDt = 0;
static_assert(kDtPwrmgrCount == 1, "this test expects a pwrmgr");
static const dt_aon_timer_t kAonTimerDt = 0;
static_assert(kDtAonTimerCount >= 1,
              "this test expects at least one aon_timer");

OTTF_DEFINE_TEST_CONFIG();

static dif_pwrmgr_t pwrmgr;
static dif_aon_timer_t aon_timer;
static dif_pwrmgr_request_sources_t wakeup_sources;

static status_t test_init(void) {
  // Initialize aon timer to use the wdog.
  CHECK_DIF_OK(dif_aon_timer_init_from_dt(kAonTimerDt, &aon_timer));
  TRY(dif_pwrmgr_init_from_dt(kPwrmgrDt, &pwrmgr));
  TRY(dif_pwrmgr_find_request_source(
      &pwrmgr, kDifPwrmgrReqTypeWakeup, dt_aon_timer_instance_id(kAonTimerDt),
      kDtAonTimerWakeupWkupReq, &wakeup_sources));
  return OK_STATUS();
}

static status_t deep_sleep_enter(uint32_t wakeup_ticks) {
  dif_pwrmgr_domain_config_t pwrmgr_domain_cfg = 0;
  TRY(pwrmgr_testutils_enable_low_power(&pwrmgr, wakeup_sources,
                                        pwrmgr_domain_cfg));
  TRY(dif_aon_timer_wakeup_start(&aon_timer, wakeup_ticks, 0));
  LOG_INFO("Going to sleep.");
  wait_for_interrupt();
  LOG_INFO("Unexpected wakeup from deep sleep.");
  return UNKNOWN();
}

static status_t deep_sleep_check(void) {
  bool wkup = TRY(pwrmgr_testutils_is_wakeup_reason(&pwrmgr, wakeup_sources));
  return OK_STATUS(wkup);
}

static status_t initialize(retention_sram_t *retram, boot_svc_retram_t *state) {
  boot_svc_msg_t msg = {0};
  boot_svc_empty_req_init(&msg.empty);
  retram->creator.boot_svc_msg = msg;
  state->state = kBootSvcTestStateCheckEmpty;
  TRY(deep_sleep_enter((uint32_t)kClockFreqAonHz));
  return INTERNAL();
}

static status_t check_empty(retention_sram_t *retram,
                            boot_svc_retram_t *state) {
  if (!TRY(deep_sleep_check())) {
    LOG_ERROR("Expected wakup from deep sleep");
    return INTERNAL();
  }
  boot_svc_msg_t msg = retram->creator.boot_svc_msg;
  TRY(boot_svc_header_check(&msg.header));
  // We expect the `EmptyReqType` here because the ROM_EXT should not process
  // boot_svc requests when waking from deep sleep.
  TRY_CHECK(msg.header.type == kBootSvcEmptyReqType);
  state->state = kBootSvcTestStateFinal;
  return OK_STATUS();
}

static status_t empty_message_test(void) {
  TRY(test_init());
  retention_sram_t *retram = retention_sram_get();
  TRY(boot_svc_test_init(retram, kBootSvcTestWakeup));
  boot_svc_retram_t *state = (boot_svc_retram_t *)&retram->owner;

  for (;;) {
    LOG_INFO("Test state = %d", state->state);
    switch (state->state) {
      case kBootSvcTestStateInit:
        TRY(initialize(retram, state));
        break;
      case kBootSvcTestStateCheckEmpty:
        TRY(check_empty(retram, state));
        break;
      case kBootSvcTestStateFinal:
        return OK_STATUS();
      default:
        return UNKNOWN();
    }
  }
}

bool test_main(void) {
  status_t sts = empty_message_test();
  if (status_err(sts)) {
    LOG_ERROR("boot_svc_wakeup_test: %r", sts);
  }
  return status_ok(sts);
}
