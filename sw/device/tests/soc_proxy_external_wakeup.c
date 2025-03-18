// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/status.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"
#include "sw/device/lib/testing/autogen/isr_testutils.h"

OTTF_DEFINE_TEST_CONFIG();

static dif_pwrmgr_t pwrmgr;
static dif_rv_plic_t plic;

static plic_isr_ctx_t plic_ctx = {.rv_plic = &plic,
                                  .hart_id = kTopDarjeelingPlicTargetIbex0};

static pwrmgr_isr_ctx_t pwrmgr_isr_ctx = {
    .pwrmgr = &pwrmgr,
    .plic_pwrmgr_start_irq_id = kTopDarjeelingPlicIrqIdPwrmgrAonWakeup,
    .expected_irq = kDifPwrmgrIrqWakeup,
    .is_only_irq = true};

bool test_main(void) {
  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_DARJEELING_PWRMGR_AON_BASE_ADDR), &pwrmgr));
  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_DARJEELING_RV_PLIC_BASE_ADDR), &plic));

  // Enable global and external IRQ in Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  // Enable wakeup interrupt output from Power Manager.
  rv_plic_testutils_irq_range_enable(&plic, kTopDarjeelingPlicTargetIbex0,
                                     kTopDarjeelingPlicIrqIdPwrmgrAonWakeup,
                                     kTopDarjeelingPlicIrqIdPwrmgrAonWakeup);
  CHECK_DIF_OK(dif_pwrmgr_irq_set_enabled(&pwrmgr, 0, kDifToggleEnabled));

  // Get currently enabled sources for wakeup requests in Power Manager.
  dif_pwrmgr_request_sources_t wakeup_req_srcs;
  CHECK_DIF_OK(dif_pwrmgr_get_request_sources(&pwrmgr, kDifPwrmgrReqTypeWakeup,
                                              &wakeup_req_srcs));

  // Enable external wakeup request in Power Manager.
  const dif_pwrmgr_request_sources_t ext_wkup_req =
      (1u << kTopDarjeelingPowerManagerWakeUpsSocProxyWkupExternalReq);
  wakeup_req_srcs |= ext_wkup_req;
  CHECK_DIF_OK(dif_pwrmgr_set_request_sources(
      &pwrmgr, kDifPwrmgrReqTypeWakeup, wakeup_req_srcs, kDifToggleEnabled));
  LOG_INFO("Power Manager configured.");
  CHECK_DIF_OK(
      dif_pwrmgr_low_power_set_enabled(&pwrmgr, /*new_state=*/kDifToggleEnabled,
                                       /*sync_state=*/kDifToggleEnabled));
  test_status_set(kTestStatusInWfi);
  wait_for_interrupt();
  test_status_set(kTestStatusInTest);

  // Wait for wakeup request to show up in Power Manager.
  while (true) {
    dif_pwrmgr_request_sources_t cur_wakeup_srcs;
    CHECK_DIF_OK(dif_pwrmgr_get_current_request_sources(
        &pwrmgr, kDifPwrmgrReqTypeWakeup, &cur_wakeup_srcs));
    if (cur_wakeup_srcs & ext_wkup_req) {
      LOG_INFO("External wakeup request detected.");
      break;
    }
    busy_spin_micros(5);
  }

  return true;
}

// Interrupt service routine
void ottf_external_isr(void) {
  dif_pwrmgr_irq_t irq_id;
  top_darjeeling_plic_peripheral_t peripheral;

  isr_testutils_pwrmgr_isr(plic_ctx, pwrmgr_isr_ctx, &peripheral, &irq_id);

  // Check that peripheral and IRQ ID are correct.
  CHECK(peripheral == kTopDarjeelingPlicPeripheralPwrmgrAon,
        "IRQ peripheral %d is incorrect!", peripheral);
  CHECK(irq_id == kDifPwrmgrIrqWakeup, "IRQ ID %d is incorrect!", irq_id);
}
