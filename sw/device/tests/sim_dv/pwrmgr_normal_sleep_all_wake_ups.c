// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_adc_ctrl.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_sensor_ctrl.h"
#include "sw/device/lib/dif/dif_sysrst_ctrl.h"
#include "sw/device/lib/irq.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/usbdev.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "pwrmgr_regs.h"
#include "sw/device/lib/testing/autogen/isr_testutils.h"

/*
  PWRMGR NORMAL SLEEP ALL WAKE UPS test

  This test runs power manager wake up from deep sleep mode by
  wake up inputs.

  There are 6 wake up inputs.
  0: sysrst_ctrl
  1: adc_ctrl
  2: pinmux
  3: usb
  4: aon_timer
  5: sensor_ctrl

 */

OTTF_DEFINE_TEST_CONFIG();

static const uint32_t kPinmuxWkupDetector5 = 5;

static dif_pwrmgr_t pwrmgr;
static dif_rv_plic_t rv_plic;
static dif_sysrst_ctrl_t sysrst_ctrl;
static dif_adc_ctrl_t adc_ctrl;
static dif_pinmux_t pinmux;
static dif_usbdev_t usbdev;
static dif_aon_timer_t aon_timer;
static dif_sensor_ctrl_t sensor_ctrl;

static plic_isr_ctx_t plic_ctx = {.rv_plic = &rv_plic,
                                  .hart_id = kTopEarlgreyPlicTargetIbex0};

static pwrmgr_isr_ctx_t pwrmgr_isr_ctx = {
    .pwrmgr = &pwrmgr,
    .plic_pwrmgr_start_irq_id = kTopEarlgreyPlicIrqIdPwrmgrAonWakeup,
    .expected_irq = kDifPwrmgrIrqWakeup,
    .is_only_irq = true};

typedef struct test_wakeup_sources {
  /**
   * Name of the device.
   */
  const char *name;
  /**
   * Handle to the DIF object for this device.
   */
  void *dif_handle;
  /**
   * Wakeup Sources
   */
  dif_pwrmgr_request_sources_t wakeup_src;
  /**
   * Configuration and initialization actions for the device.
   * This will be passed the value of `dif` above.
   */
  void (*config)(void *dif);
} test_wakeup_sources_t;

/**
 * sysrst_ctrl config for test #1
 * . set sysrst_ctrl.KEY_INTR_CTL.pwrb_in_H2L to 1
 * . use IOR13 as pwrb_in
 */
static void prgm_sysrst_ctrl_wakeup(void *dif) {
  dif_sysrst_ctrl_input_change_config_t config = {
      .input_changes = kDifSysrstCtrlInputPowerButtonH2L,
      .debounce_time_threshold = 1,  // 5us
  };
  CHECK_DIF_OK(dif_sysrst_ctrl_input_change_detect_configure(dif, config));
  CHECK_DIF_OK(dif_pinmux_input_select(
      &pinmux, kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonPwrbIn,
      kTopEarlgreyPinmuxInselIor13));
}

/**
 * adc_ctrl config for test #2
 * . enable filter 5 and set voltage range (0,200)
 */
static void prgm_adc_ctrl_wakeup(void *dif) {
  dif_adc_ctrl_config_t cfg = {
      .mode = kDifAdcCtrlLowPowerScanMode,
      .power_up_time_aon_cycles = 6,
      .wake_up_time_aon_cycles = 100,
      .num_low_power_samples = 2,
      .num_normal_power_samples = 8,
  };
  CHECK_DIF_OK(dif_adc_ctrl_configure(dif, cfg));

  dif_adc_ctrl_filter_config_t filter_cfg = {
      .filter = kDifAdcCtrlFilter5,
      .min_voltage = 0,
      .max_voltage = 200,
      .in_range = true,
      .generate_wakeup_on_match = true,
      .generate_irq_on_match = false,
  };

  CHECK_DIF_OK(dif_adc_ctrl_configure_filter(dif, kDifAdcCtrlChannel0,
                                             filter_cfg, kDifToggleEnabled));
  CHECK_DIF_OK(dif_adc_ctrl_configure_filter(dif, kDifAdcCtrlChannel1,
                                             filter_cfg, kDifToggleEnabled));
  CHECK_DIF_OK(dif_adc_ctrl_filter_match_wakeup_set_enabled(
      dif, kDifAdcCtrlFilter5, kDifToggleEnabled));
  CHECK_DIF_OK(dif_adc_ctrl_set_enabled(dif, kDifToggleEnabled));
}

/**
 * pinmux config for test #3
 * . use IOB7 as an input
 * . set posedge detection
 */
static void prgm_pinmux_wakeup(void *dif) {
  dif_pinmux_wakeup_config_t detector_cfg = {
      .signal_filter = kDifToggleDisabled,
      .pad_type = kDifPinmuxPadKindMio,
      .pad_select = kTopEarlgreyPinmuxInselIob7,
      .mode = kDifPinmuxWakeupModePositiveEdge,
      .counter_threshold = 0 /* Don't need for posedge detection */,
  };
  CHECK_DIF_OK(dif_pinmux_wakeup_detector_enable(dif, kPinmuxWkupDetector5,
                                                 detector_cfg));
}

/**
 * usb config for test #4
 * . Fake low power entry through usb
 * . Force usb to output suspend indication
 * (*dif) handle is not used but leave as is
 * to be called from execute_test
 */
static void prgm_usb_wakeup(void *dif) {
  usbdev_set_wake_module_active(true);
  usbdev_force_dx_pullup(kDpSel, true);
  usbdev_force_dx_pullup(kDnSel, false);

  LOG_INFO("prgm_usb_wakeup: wait 20us (usb)");
  // Give the hardware a chance to recognize the wakeup values are the same.
  busy_spin_micros(20);  // 20us
}

/**
 * aon timer config for test #5
 * set wakeup signal in 50us
 */
static void prgm_aontimer_wakeup(void *dif) {
  aon_timer_testutils_wakeup_config(dif, 10);
}

/**
 * sensor ctrl config for test #6
 * setup event trigger0
 */
static void prgm_sensor_ctrl_wakeup(void *dif) {
  CHECK_DIF_OK(
      dif_sensor_ctrl_set_ast_event_trigger(dif, 0, kDifToggleEnabled));
}
static const test_wakeup_sources_t kTestWakeupSources[] = {
    {
        .name = "SYSRST_CTRL",
        .dif_handle = &sysrst_ctrl,
        .wakeup_src = kDifPwrmgrWakeupRequestSourceOne,
        .config = prgm_sysrst_ctrl_wakeup,
    },
    {
        .name = "ADC_CTRL",
        .dif_handle = &adc_ctrl,
        .wakeup_src = kDifPwrmgrWakeupRequestSourceTwo,
        .config = prgm_adc_ctrl_wakeup,
    },
    {
        .name = "PINMUX",
        .dif_handle = &pinmux,
        .wakeup_src = kDifPwrmgrWakeupRequestSourceThree,
        .config = prgm_pinmux_wakeup,
    },
    {
        .name = "USB",
        .dif_handle = &usbdev,
        .wakeup_src = kDifPwrmgrWakeupRequestSourceFour,
        .config = prgm_usb_wakeup,
    },
    {
        .name = "AONTIMER",
        .dif_handle = &aon_timer,
        .wakeup_src = kDifPwrmgrWakeupRequestSourceFive,
        .config = prgm_aontimer_wakeup,
    },
    {
        .name = "SENSOR_CTRL",
        .dif_handle = &sensor_ctrl,
        .wakeup_src = kDifPwrmgrWakeupRequestSourceSix,
        .config = prgm_sensor_ctrl_wakeup,
    },
};

/**
 * External interrupt handler.
 */
void ottf_external_isr(void) {
  dif_pwrmgr_irq_t irq_id;
  top_earlgrey_plic_peripheral_t peripheral;

  isr_testutils_pwrmgr_isr(plic_ctx, pwrmgr_isr_ctx, &peripheral, &irq_id);

  // Check that both the peripheral and the irq id is correct
  CHECK(peripheral == kTopEarlgreyPlicPeripheralPwrmgrAon,
        "IRQ peripheral: %d is incorrect", peripheral);
  CHECK(irq_id == kDifPwrmgrIrqWakeup, "IRQ ID: %d is incorrect", irq_id);
}

static void execute_test(uint32_t wakeup_source) {
  // Configure wakeup device
  kTestWakeupSources[wakeup_source].config(
      kTestWakeupSources[wakeup_source].dif_handle);
  // Normal sleep
  dif_pwrmgr_domain_config_t cfg;
  CHECK_DIF_OK(dif_pwrmgr_get_domain_config(&pwrmgr, &cfg));
  cfg = cfg & (kDifPwrmgrDomainOptionIoClockInLowPower |
               kDifPwrmgrDomainOptionUsbClockInLowPower |
               kDifPwrmgrDomainOptionUsbClockInActivePower |
               kDifPwrmgrDomainOptionMainPowerInLowPower);

  pwrmgr_testutils_enable_low_power(
      &pwrmgr, kTestWakeupSources[wakeup_source].wakeup_src, cfg);
  LOG_INFO("Issue WFI to enter sleep %d", wakeup_source);
  wait_for_interrupt();
}

/**
 * Check pwrmgr wakeup status is avalable.
 */
static bool get_wakeup_status(void) {
  dif_pwrmgr_request_sources_t wake_req = -1;
  CHECK_DIF_OK(dif_pwrmgr_get_current_request_sources(
      &pwrmgr, kDifPwrmgrReqTypeWakeup, &wake_req));
  return (wake_req > 0);
}

/**
 * Clean up wakup sources.
 */
static void cleanup(uint32_t test_idx) {
  switch (test_idx) {
    case PWRMGR_PARAM_SYSRST_CTRL_AON_WKUP_REQ_IDX:
      CHECK_DIF_OK(dif_sysrst_ctrl_ulp_wakeup_clear_status(&sysrst_ctrl));
      break;
    case PWRMGR_PARAM_ADC_CTRL_AON_WKUP_REQ_IDX:
      CHECK_DIF_OK(dif_adc_ctrl_filter_match_wakeup_set_enabled(
          &adc_ctrl, kDifAdcCtrlFilter5, kDifToggleDisabled));
      break;
    case PWRMGR_PARAM_PINMUX_AON_PIN_WKUP_REQ_IDX:
      CHECK_DIF_OK(dif_pinmux_wakeup_cause_clear(&pinmux));
      break;
    case PWRMGR_PARAM_PINMUX_AON_USB_WKUP_REQ_IDX:
      usbdev_set_wake_module_active(false);
      CHECK_DIF_OK(dif_pinmux_wakeup_cause_clear(&pinmux));
      break;
    case PWRMGR_PARAM_AON_TIMER_AON_WKUP_REQ_IDX:
      CHECK_DIF_OK(dif_aon_timer_wakeup_stop(&aon_timer));
      CHECK_DIF_OK(dif_aon_timer_clear_wakeup_cause(&aon_timer));
      break;
    case PWRMGR_PARAM_SENSOR_CTRL_WKUP_REQ_IDX:
      // clear event trigger
      CHECK_DIF_OK(dif_sensor_ctrl_set_ast_event_trigger(&sensor_ctrl, 0,
                                                         kDifToggleDisabled));
      CHECK_DIF_OK(dif_sensor_ctrl_clear_recov_event(&sensor_ctrl, 0));
      break;
    default:
      LOG_ERROR("unknown test index %d", test_idx);
  }

  // Ensure the de-asserted events have cleared from the wakeup pipeline
  // within 30us.
  IBEX_SPIN_FOR(!get_wakeup_status(), 100);
  CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_clear(&pwrmgr));
}

bool test_main(void) {
  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  // device init
  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));
  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &rv_plic));
  CHECK_DIF_OK(dif_sysrst_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SYSRST_CTRL_AON_BASE_ADDR),
      &sysrst_ctrl));
  CHECK_DIF_OK(dif_adc_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_ADC_CTRL_AON_BASE_ADDR), &adc_ctrl));
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  CHECK_DIF_OK(dif_usbdev_init(
      mmio_region_from_addr(TOP_EARLGREY_USBDEV_BASE_ADDR), &usbdev));
  CHECK_DIF_OK(dif_aon_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR), &aon_timer));
  CHECK_DIF_OK(dif_sensor_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SENSOR_CTRL_BASE_ADDR), &sensor_ctrl));

  // Enable all the AON interrupts used in this test.
  rv_plic_testutils_irq_range_enable(&rv_plic, kTopEarlgreyPlicTargetIbex0,
                                     kTopEarlgreyPlicIrqIdPwrmgrAonWakeup,
                                     kTopEarlgreyPlicIrqIdPwrmgrAonWakeup);

  // Enable pwrmgr interrupt
  CHECK_DIF_OK(dif_pwrmgr_irq_set_enabled(&pwrmgr, 0, kDifToggleEnabled));

  if (pwrmgr_testutils_is_wakeup_reason(&pwrmgr, 0)) {
    LOG_INFO("POR reset");

    for (size_t i = 0; i < PWRMGR_PARAM_NUM_WKUPS; ++i) {
      LOG_INFO("Test %d begin", i);
      execute_test(i);
      dif_pwrmgr_wakeup_reason_t wakeup_reason;
      CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_get(&pwrmgr, &wakeup_reason));
      CHECK(pwrmgr_testutils_is_wakeup_reason(
                &pwrmgr, kTestWakeupSources[i].wakeup_src) == true,
            "wakeup reason wrong exp:%d  obs:%d",
            kTestWakeupSources[i].wakeup_src, wakeup_reason);
      LOG_INFO("Woke up by source %d", i);
      cleanup(i);
      LOG_INFO("clean up done source %d", i);
    }
    return true;
  }

  return false;
}
