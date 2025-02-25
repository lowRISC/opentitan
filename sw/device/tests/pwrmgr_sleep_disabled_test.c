// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

OTTF_DEFINE_TEST_CONFIG();

static_assert(kDtPwrmgrCount == 1, "this test expects exactly one pwrmgr");
static const dt_pwrmgr_t kPwrmgrDt = 0;
static_assert(kDtRvPlicCount == 1, "this test expects exactly one rv_plic");
static const dt_rv_plic_t kRvPlicDt = 0;
static_assert(kDtAonTimerCount >= 1,
              "this test expects at least one aon_timer");
static const dt_aon_timer_t kAonTimerDt = 0;

static const uint32_t kPlicTarget = 0;
static const uint32_t kSourcePriority = 1;
static dif_aon_timer_t aon_timer;
static dif_rv_plic_t plic;

// Volatile globals accessed from the ISR.
static volatile dif_aon_timer_irq_t irq;
static volatile bool interrupt_serviced = false;

static bool is_pwrmgr_irq_pending(void) {
  bool status;
  dif_rv_plic_irq_id_t irq_id =
      dt_pwrmgr_irq_to_plic_id(kPwrmgrDt, kDtPwrmgrIrqWakeup);
  CHECK_DIF_OK(dif_rv_plic_irq_is_pending(&plic, irq_id, &status));
  return status;
}

/**
 * External interrupt handler.
 */
bool ottf_handle_irq(uint32_t *exc_info, dt_instance_id_t devid,
                     dif_rv_plic_irq_id_t irq_id) {
  if (devid == dt_aon_timer_instance_id(kAonTimerDt) &&
      irq_id == dt_aon_timer_irq_to_plic_id(kAonTimerDt,
                                            kDtAonTimerIrqWkupTimerExpired)) {
    CHECK_DIF_OK(dif_aon_timer_wakeup_stop(&aon_timer));
    CHECK_DIF_OK(dif_aon_timer_irq_acknowledge(&aon_timer, irq));
    interrupt_serviced = true;
    return true;
  } else {
    return false;
  }
}

bool test_main(void) {
  dif_pwrmgr_t pwrmgr;

  // Issue a wakeup signal in 200us through the AON timer.
  //
  // Adjust the cycles for Verilator since it runs on different clock
  // frequencies.
  uint64_t wakeup_cycles = 0;
  uint32_t wakeup_time_micros = 200;
  CHECK_STATUS_OK(aon_timer_testutils_get_aon_cycles_64_from_us(
      wakeup_time_micros, &wakeup_cycles));
  if (kDeviceType == kDeviceSimVerilator) {
    wakeup_cycles *= 10;
  }

  // Initialize unit difs.
  CHECK_DIF_OK(dif_pwrmgr_init_from_dt(kPwrmgrDt, &pwrmgr));
  CHECK_DIF_OK(dif_aon_timer_init_from_dt(kAonTimerDt, &aon_timer));
  CHECK_DIF_OK(dif_rv_plic_init_from_dt(kRvPlicDt, &plic));
  dif_pwrmgr_request_sources_t wakeup_sources;
  CHECK_DIF_OK(dif_pwrmgr_find_request_source(
      &pwrmgr, kDifPwrmgrReqTypeWakeup, dt_aon_timer_instance_id(kAonTimerDt),
      kDtAonTimerWakeupWkupReq, &wakeup_sources));

  // Notice we are clearing rstmgr's RESET_INFO, so after the aon wakeup there
  // is only one bit set.
  if (UNWRAP(pwrmgr_testutils_is_wakeup_reason(&pwrmgr, 0)) == true) {
    LOG_INFO("POR reset");

    // Enable aon wakeup.
    CHECK_DIF_OK(dif_pwrmgr_set_request_sources(
        &pwrmgr, kDifPwrmgrReqTypeWakeup, wakeup_sources, kDifToggleEnabled));
    LOG_INFO("Enabled aon wakeup");

    // Enable the AON wakeup interrupt.
    dif_rv_plic_irq_id_t plic_id = dt_aon_timer_irq_to_plic_id(
        kAonTimerDt, kDtAonTimerIrqWkupTimerExpired);
    CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(&plic, plic_id, kPlicTarget,
                                             kDifToggleEnabled));
    LOG_INFO("Enabled aon wakeup interrupt");
    CHECK_DIF_OK(dif_rv_plic_irq_set_priority(&plic, plic_id, kSourcePriority));
    LOG_INFO("Set aon wakeup interrupt priority");

    // Enable pwrmgr wakeup interrupt, so it triggers an interrupt even though
    // it should not.
    CHECK_DIF_OK(dif_pwrmgr_irq_set_enabled(&pwrmgr, kDifPwrmgrIrqWakeup,
                                            kDifToggleEnabled));
    plic_id = dt_pwrmgr_irq_to_plic_id(kPwrmgrDt, kDtPwrmgrIrqWakeup);
    CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(&plic, plic_id, kPlicTarget,
                                             kDifToggleEnabled));
    LOG_INFO("Enabled pwrmgr wakeup interrupt");
    CHECK_DIF_OK(dif_rv_plic_irq_set_priority(&plic, plic_id, kSourcePriority));
    LOG_INFO("Set pwrmgr wakeup interrupt priority");

    // Prepare for interrupt.
    LOG_INFO("Issue WFI without sleep");

    // Start wakeup timer close enough to the WFI to avoid it happening
    // too early.
    CHECK_STATUS_OK(
        aon_timer_testutils_wakeup_config(&aon_timer, wakeup_cycles));
    irq_global_ctrl(true);
    irq_external_ctrl(true);
    ATOMIC_WAIT_FOR_INTERRUPT(interrupt_serviced);

    LOG_INFO("The interrupt was processed");
    // And to be extra safe, check there is no pwrmgr interrupt pending.
    CHECK(!is_pwrmgr_irq_pending());

    return true;
  } else if (UNWRAP(pwrmgr_testutils_is_wakeup_reason(
                 &pwrmgr, wakeup_sources)) == true) {
    LOG_ERROR("Unexpected wakeup request");
    return false;
  }

  return false;
}
