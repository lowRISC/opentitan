// Copyright lowRISC contributors.
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

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "sw/device/lib/testing/autogen/isr_testutils.h"

OTTF_DEFINE_TEST_CONFIG();

enum {
  kPowerUpTimeAonCycles = 7,
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

void ottf_external_isr(void) {
  plic_isr_ctx_t plic_ctx = {.rv_plic = &plic,
                             .hart_id = kTopEarlgreyPlicTargetIbex0};

  adc_ctrl_isr_ctx_t adc_ctrl_ctx = {
      .adc_ctrl = &adc_ctrl,
      .plic_adc_ctrl_start_irq_id = kTopEarlgreyPlicIrqIdAdcCtrlAonMatchDone,
      .expected_irq = 0,
      .is_only_irq = true};

  top_earlgrey_plic_peripheral_t peripheral;
  dif_adc_ctrl_irq_t adc_ctrl_irq;
  isr_testutils_adc_ctrl_isr(plic_ctx, adc_ctrl_ctx, &peripheral,
                             &adc_ctrl_irq);

  CHECK(peripheral == kTopEarlgreyPlicPeripheralAdcCtrlAon);
  CHECK(adc_ctrl_irq == kDifAdcCtrlIrqMatchDone);
  interrupt_serviced = true;

  // Verify this interrupt was actually expected.
  CHECK(interrupt_expected);
}

static void en_plic_irqs(dif_rv_plic_t *plic) {
  top_earlgrey_plic_irq_id_t plic_irqs[] = {
      kTopEarlgreyPlicIrqIdAdcCtrlAonMatchDone};

  for (uint32_t i = 0; i < ARRAYSIZE(plic_irqs); ++i) {
    CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(
        plic, plic_irqs[i], kTopEarlgreyPlicTargetIbex0, kDifToggleEnabled));

    // Assign a default priority
    CHECK_DIF_OK(dif_rv_plic_irq_set_priority(plic, plic_irqs[i], 0x1));
  }

  // Enable the external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);
}

bool test_main(void) {
  dif_pwrmgr_t pwrmgr;
  dif_rstmgr_t rstmgr;

  CHECK_DIF_OK(dif_adc_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_ADC_CTRL_AON_BASE_ADDR), &adc_ctrl));
  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));
  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &plic));

  // Enable adc interrupts.
  CHECK_DIF_OK(dif_adc_ctrl_irq_set_enabled(&adc_ctrl, kDifAdcCtrlIrqMatchDone,
                                            kDifToggleEnabled));

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
    CHECK_STATUS_OK(pwrmgr_testutils_enable_low_power(
        &pwrmgr, kDifPwrmgrWakeupRequestSourceTwo, 0));
    // Enter low power mode.
    LOG_INFO("Issued WFI to enter sleep.");
    test_status_set(kTestStatusInWfi);
    wait_for_interrupt();
  } else if (UNWRAP(pwrmgr_testutils_is_wakeup_reason(
                 &pwrmgr, kDifPwrmgrWakeupRequestSourceTwo)) == true) {
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
