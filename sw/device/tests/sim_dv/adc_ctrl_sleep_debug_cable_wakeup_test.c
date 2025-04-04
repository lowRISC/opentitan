// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_adc_ctrl.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

OTTF_DEFINE_TEST_CONFIG();

static const dt_adc_ctrl_t kAdcCtrlDt = 0;
static_assert(kDtAdcCtrlCount == 1, "this test expects a adc_ctrl");
static const dt_rv_plic_t kRvPlicDt = 0;
static_assert(kDtRvPlicCount == 1, "this test expects exactly one rv_plic");
static const dt_rstmgr_t kRstmgrDt = 0;
static_assert(kDtRstmgrCount == 1, "this test expects a rstmgr");
static const dt_pwrmgr_t kPwrmgrDt = 0;
static_assert(kDtPwrmgrCount == 1, "this test expects a pwrmgr");

enum {
  kPowerUpTimeAonCycles = 7,
  kPlicTarget = 0,
};

// These constants will be setup from the testbench
// using sw_symbol_backdoor_overwrite.

static volatile const uint8_t kNumLowPowerSamples;
static volatile const uint8_t kNumNormalPowerSamples;
static volatile const uint8_t kWakeUpTimeAonCycles;

static volatile const uint8_t kChannel0MaxLowByte;
static volatile const uint8_t kChannel0MaxHighByte;
static volatile const uint8_t kChannel0MinLowByte;
static volatile const uint8_t kChannel0MinHighByte;

static volatile const uint8_t kChannel1MaxLowByte;
static volatile const uint8_t kChannel1MaxHighByte;
static volatile const uint8_t kChannel1MinLowByte;
static volatile const uint8_t kChannel1MinHighByte;

static void configure_adc_ctrl(const dif_adc_ctrl_t *adc_ctrl) {
  CHECK_DIF_OK(dif_adc_ctrl_set_enabled(adc_ctrl, kDifToggleDisabled));
  CHECK_DIF_OK(dif_adc_ctrl_reset(adc_ctrl));
  CHECK_DIF_OK(dif_adc_ctrl_configure(
      adc_ctrl, (dif_adc_ctrl_config_t){
                    .mode = kDifAdcCtrlLowPowerScanMode,
                    .num_low_power_samples = kNumLowPowerSamples,
                    .num_normal_power_samples = kNumNormalPowerSamples,
                    .power_up_time_aon_cycles = kPowerUpTimeAonCycles,
                    .wake_up_time_aon_cycles = kWakeUpTimeAonCycles}));
}

static dif_adc_ctrl_t adc_ctrl;
static dif_rv_plic_t plic;
static volatile bool interrupt_expected = false;
static volatile bool interrupt_serviced = false;

bool ottf_handle_irq(uint32_t *exc_info, dt_instance_id_t devid,
                     dif_rv_plic_irq_id_t irq_id) {
  if (devid == dt_adc_ctrl_instance_id(kAdcCtrlDt) &&
      irq_id ==
          dt_adc_ctrl_irq_to_plic_id(kAdcCtrlDt, kDtAdcCtrlIrqMatchPending)) {
    // Verify this interrupt was actually expected.
    CHECK(interrupt_expected);
    interrupt_serviced = true;
    CHECK_DIF_OK(
        dif_adc_ctrl_irq_acknowledge(&adc_ctrl, kDtAdcCtrlIrqMatchPending));
    return true;
  } else {
    return false;
  }
}

static void en_plic_irqs(dif_rv_plic_t *plic) {
  dif_rv_plic_irq_id_t plic_id =
      dt_adc_ctrl_irq_to_plic_id(kAdcCtrlDt, kDtAdcCtrlIrqMatchPending);
  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(plic, plic_id, kPlicTarget,
                                           kDifToggleEnabled));

  // Assign a default priority
  CHECK_DIF_OK(dif_rv_plic_irq_set_priority(plic, plic_id, 0x1));

  // Enable the external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);
}

bool test_main(void) {
  dif_pwrmgr_t pwrmgr;
  dif_rstmgr_t rstmgr;

  CHECK_DIF_OK(dif_adc_ctrl_init_from_dt(kAdcCtrlDt, &adc_ctrl));
  CHECK_DIF_OK(dif_pwrmgr_init_from_dt(kPwrmgrDt, &pwrmgr));
  CHECK_DIF_OK(dif_rstmgr_init_from_dt(kRstmgrDt, &rstmgr));
  CHECK_DIF_OK(dif_rv_plic_init_from_dt(kRvPlicDt, &plic));

  dif_pwrmgr_request_sources_t wakeup_sources;
  CHECK_DIF_OK(dif_pwrmgr_find_request_source(
      &pwrmgr, kDifPwrmgrReqTypeWakeup, dt_adc_ctrl_instance_id(kAdcCtrlDt),
      kDtAdcCtrlWakeupWkupReq, &wakeup_sources));

  // Enable adc interrupts.
  CHECK_DIF_OK(dif_adc_ctrl_irq_set_enabled(
      &adc_ctrl, kDifAdcCtrlIrqMatchPending, kDifToggleEnabled));

  uint16_t channel0_filter0_max =
      (uint16_t)(kChannel0MaxHighByte << 8) | kChannel0MaxLowByte;
  uint16_t channel0_filter0_min =
      (uint16_t)(kChannel0MinHighByte << 8) | kChannel0MinLowByte;
  uint16_t channel1_filter0_max =
      (uint16_t)(kChannel1MaxHighByte << 8) | kChannel1MaxLowByte;
  uint16_t channel1_filter0_min =
      (uint16_t)(kChannel1MinHighByte << 8) | kChannel1MinLowByte;

  // Assuming the chip hasn't slept yet, wakeup reason should be empty.
  if (UNWRAP(pwrmgr_testutils_is_wakeup_reason(&pwrmgr, 0)) == true) {
    LOG_INFO("POR reset.");
    interrupt_expected = false;
    en_plic_irqs(&plic);

    CHECK(UNWRAP(
        rstmgr_testutils_is_reset_info(&rstmgr, kDifRstmgrResetInfoPor)));

    // Setup ADC configuration.
    configure_adc_ctrl(&adc_ctrl);

    // Setup ADC filters. There is one filter for each channel.
    CHECK_DIF_OK(dif_adc_ctrl_configure_filter(
        &adc_ctrl, kDifAdcCtrlChannel0,
        (dif_adc_ctrl_filter_config_t){.filter = kDifAdcCtrlFilter0,
                                       .generate_irq_on_match = true,
                                       .generate_wakeup_on_match = true,
                                       .in_range = true,
                                       .max_voltage = channel0_filter0_max,
                                       .min_voltage = channel0_filter0_min},
        kDifToggleDisabled));
    CHECK_DIF_OK(dif_adc_ctrl_configure_filter(
        &adc_ctrl, kDifAdcCtrlChannel1,
        (dif_adc_ctrl_filter_config_t){.filter = kDifAdcCtrlFilter0,
                                       .generate_irq_on_match = true,
                                       .generate_wakeup_on_match = true,
                                       .in_range = true,
                                       .max_voltage = channel1_filter0_max,
                                       .min_voltage = channel1_filter0_min},
        kDifToggleDisabled));

    // enable filters.
    CHECK_DIF_OK(dif_adc_ctrl_filter_set_enabled(
        &adc_ctrl, kDifAdcCtrlChannel0, kDifAdcCtrlFilter0, kDifToggleEnabled));
    CHECK_DIF_OK(dif_adc_ctrl_filter_set_enabled(
        &adc_ctrl, kDifAdcCtrlChannel1, kDifAdcCtrlFilter0, kDifToggleEnabled));

    CHECK_DIF_OK(dif_adc_ctrl_set_enabled(&adc_ctrl, kDifToggleEnabled));

    // Setup low power.
    CHECK_STATUS_OK(rstmgr_testutils_pre_reset(&rstmgr));
    CHECK_STATUS_OK(
        pwrmgr_testutils_enable_low_power(&pwrmgr, wakeup_sources, 0));
    // Enter low power mode.
    LOG_INFO("Issued WFI to enter sleep.");
    test_status_set(kTestStatusInWfi);
    wait_for_interrupt();
  } else if (UNWRAP(pwrmgr_testutils_is_wakeup_reason(
                 &pwrmgr, wakeup_sources)) == true) {
    LOG_INFO("Wakeup reset.");
    interrupt_expected = true;
    en_plic_irqs(&plic);

    CHECK(UNWRAP(rstmgr_testutils_is_reset_info(
        &rstmgr, kDifRstmgrResetInfoLowPowerExit)));
    uint16_t adc_value;
    CHECK_DIF_OK(dif_adc_ctrl_get_triggered_value(
        &adc_ctrl, kDifAdcCtrlChannel0, &adc_value));
    CHECK(channel0_filter0_min <= adc_value &&
          adc_value <= channel0_filter0_max);

    CHECK_DIF_OK(dif_adc_ctrl_get_triggered_value(
        &adc_ctrl, kDifAdcCtrlChannel1, &adc_value));
    CHECK(channel1_filter0_min <= adc_value &&
          adc_value <= channel1_filter0_max);

    // Interrupt should have been serviced.
    CHECK(interrupt_serviced);
    return true;

  } else {
    dif_pwrmgr_wakeup_reason_t wakeup_reason;
    CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_get(&pwrmgr, &wakeup_reason));
    LOG_ERROR("Unexpected wakeup detected: type = %d, request_source = %d",
              wakeup_reason.types, wakeup_reason.request_sources);
    return false;
  }
  return false;
}
