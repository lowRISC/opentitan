// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_adc_ctrl.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_sysrst_ctrl.h"
#include "sw/device/lib/dif/dif_usbdev.h"
#include "sw/device/lib/irq.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "pwrmgr_regs.h"
#include "sw/device/lib/testing/autogen/isr_testutils.h"

/*
  PWRMGR DEEP SLEEP ALL WAKE UPS TEST

  This test runs power manager wake up from deep sleep mode by
  wake up inputs.

  There are 6 wake up inputs.
  0: sysrst_ctrl
  1: adc_ctrl
  2: pinmux
  3: usb
  4: aon_timer
  5: sensor_ctrl

  #5 is excluded because sensor_ctrl is not in the aon domain.
 */

#define PINMUX_WKUP_DETECTOR5 5

OTTF_DEFINE_TEST_CONFIG();

static dif_pwrmgr_t pwrmgr;
static dif_rv_plic_t rv_plic;
static dif_sysrst_ctrl_t sysrst_ctrl;
static dif_adc_ctrl_t adc_ctrl;
static dif_pinmux_t pinmux;
static dif_usbdev_t usbdev;
static dif_aon_timer_t aon_timer;
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
   * Wakeup Sources.
   */
  dif_pwrmgr_request_sources_t wakeup_src;
  /**
   * Configuration and initialization actions for the device.
   * This will be passed the value of `dif` above.
   */
  void (*config)(void *dif);
} test_wakeup_sources_t;

/**
 * Program sysrst_ctrl config for test #1.
 * . Set sysrst_ctrl.KEY_INTR_CTL.pwrb_in_H2L to 1.
 * . Use IOR13 as pwrb_in.
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
 * Program adc_ctrl config for test #2.
 * . Enable filter 5 and set voltage range between (0,200).
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
 * Program pinmux config for test #3.
 * . Use IOB7 as an input.
 * . Set posedge detection.
 */
static void prgm_pinmux_wakeup(void *dif) {
  dif_pinmux_wakeup_config_t detector_cfg = {
      .signal_filter = kDifToggleDisabled,
      .pad_type = kDifPinmuxPadKindMio,
      .pad_select = kTopEarlgreyPinmuxInselIob7,
      .mode = kDifPinmuxWakeupModePositiveEdge,
      .counter_threshold = 0 /* Don't need for posedge detection */,
  };
  CHECK_DIF_OK(dif_pinmux_wakeup_detector_enable(dif, PINMUX_WKUP_DETECTOR5,
                                                 detector_cfg));
}

/**
 * Program usb config for test #4.
 * . Fake low power entry through usb.
 * . Force wake detection module active.
 */
static void prgm_usb_wakeup(void *dif) {
  dif_usbdev_phy_pins_drive_t pins = {
      .dp_pullup_en = true,
      .dn_pullup_en = false,
  };
  CHECK_DIF_OK(dif_usbdev_set_phy_pins_state(dif, kDifToggleEnabled, pins));
  CHECK_DIF_OK(dif_usbdev_set_wake_enable(dif, kDifToggleEnabled));

  // Give the hardware a chance to recognize the wakeup values are the same.
  busy_spin_micros(20);
}

/**
 * Program aon timer config for test #5.
 * . Set wakeup signal in 50us.
 */
static void prgm_aontimer_wakeup(void *dif) {
  aon_timer_testutils_wakeup_config(dif, 10);
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
};

/**
 * External interrupt handler.
 */
void ottf_external_isr(void) {
  dif_pwrmgr_irq_t irq_id;
  top_earlgrey_plic_peripheral_t peripheral;

  isr_testutils_pwrmgr_isr(plic_ctx, pwrmgr_isr_ctx, &peripheral, &irq_id);

  // Check that both the peripheral and the irq id is correct.
  CHECK(peripheral == kTopEarlgreyPlicPeripheralPwrmgrAon,
        "IRQ peripheral: %d is incorrect", peripheral);
  CHECK(irq_id == kDifPwrmgrIrqWakeup, "IRQ ID: %d is incorrect", irq_id);
}

static void execute_test(int wakeup_source) {
  // Configure wakeup device per wakeup source.
  kTestWakeupSources[wakeup_source].config(
      kTestWakeupSources[wakeup_source].dif_handle);
  // Issuing deep sleep.
  dif_pwrmgr_domain_config_t cfg;
  CHECK_DIF_OK(dif_pwrmgr_get_domain_config(&pwrmgr, &cfg));
  // Tun off core clock and main power
  cfg = cfg & (kDifPwrmgrDomainOptionIoClockInLowPower |
               kDifPwrmgrDomainOptionUsbClockInLowPower |
               kDifPwrmgrDomainOptionUsbClockInActivePower);

  pwrmgr_testutils_enable_low_power(
      &pwrmgr, kTestWakeupSources[wakeup_source].wakeup_src, cfg);
  LOG_INFO("Issue WFI to enter sleep %d", wakeup_source);
  wait_for_interrupt();
}

/**
 * Clean up pwrmgr wakeup reason register for the next round.
 */
static void delay_n_clear(uint32_t delay_in_us) {
  busy_spin_micros(delay_in_us);
  CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_clear(&pwrmgr));
}

bool test_main(void) {
  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  // Device init.
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

  // Enable all the AON interrupts used in this test.
  rv_plic_testutils_irq_range_enable(&rv_plic, kTopEarlgreyPlicTargetIbex0,
                                     kTopEarlgreyPlicIrqIdPwrmgrAonWakeup,
                                     kTopEarlgreyPlicIrqIdPwrmgrAonWakeup);

  // Enable pwrmgr interrupt.
  CHECK_DIF_OK(dif_pwrmgr_irq_set_enabled(&pwrmgr, 0, kDifToggleEnabled));

  if (pwrmgr_testutils_is_wakeup_reason(&pwrmgr, 0)) {
    LOG_INFO("POR reset");
    execute_test(PWRMGR_PARAM_SYSRST_CTRL_AON_WKUP_REQ_IDX);
  } else if (pwrmgr_testutils_is_wakeup_reason(
                 &pwrmgr,
                 kTestWakeupSources[PWRMGR_PARAM_SYSRST_CTRL_AON_WKUP_REQ_IDX]
                     .wakeup_src)) {
    LOG_INFO("Woke up by source %d", PWRMGR_PARAM_SYSRST_CTRL_AON_WKUP_REQ_IDX);
    CHECK_DIF_OK(dif_sysrst_ctrl_ulp_wakeup_clear_status(
        kTestWakeupSources[PWRMGR_PARAM_SYSRST_CTRL_AON_WKUP_REQ_IDX]
            .dif_handle));
    delay_n_clear(30);
    execute_test(PWRMGR_PARAM_ADC_CTRL_AON_WKUP_REQ_IDX);
  } else if (pwrmgr_testutils_is_wakeup_reason(
                 &pwrmgr,
                 kTestWakeupSources[PWRMGR_PARAM_ADC_CTRL_AON_WKUP_REQ_IDX]
                     .wakeup_src)) {
    LOG_INFO("Woke up by source %d", PWRMGR_PARAM_ADC_CTRL_AON_WKUP_REQ_IDX);
    CHECK_DIF_OK(dif_adc_ctrl_filter_match_wakeup_set_enabled(
        kTestWakeupSources[PWRMGR_PARAM_ADC_CTRL_AON_WKUP_REQ_IDX].dif_handle,
        kDifAdcCtrlFilter5, kDifToggleDisabled));
    delay_n_clear(100);
    execute_test(PWRMGR_PARAM_PINMUX_AON_PIN_WKUP_REQ_IDX);
  } else if (pwrmgr_testutils_is_wakeup_reason(
                 &pwrmgr,
                 kTestWakeupSources[PWRMGR_PARAM_PINMUX_AON_PIN_WKUP_REQ_IDX]
                     .wakeup_src)) {
    LOG_INFO("Woke up by source %d", PWRMGR_PARAM_PINMUX_AON_PIN_WKUP_REQ_IDX);
    CHECK_DIF_OK(dif_pinmux_wakeup_cause_clear(&pinmux));
    delay_n_clear(30);
    execute_test(PWRMGR_PARAM_PINMUX_AON_USB_WKUP_REQ_IDX);
  } else if (pwrmgr_testutils_is_wakeup_reason(
                 &pwrmgr,
                 kTestWakeupSources[PWRMGR_PARAM_PINMUX_AON_USB_WKUP_REQ_IDX]
                     .wakeup_src)) {
    LOG_INFO("Woke up by source %d", PWRMGR_PARAM_PINMUX_AON_USB_WKUP_REQ_IDX);

    // Turn off wake up.
    CHECK_DIF_OK(dif_usbdev_set_wake_enable(&usbdev, kDifToggleDisabled));
    CHECK_DIF_OK(dif_pinmux_wakeup_cause_clear(&pinmux));
    delay_n_clear(30);
    execute_test(PWRMGR_PARAM_AON_TIMER_AON_WKUP_REQ_IDX);
  } else if (pwrmgr_testutils_is_wakeup_reason(
                 &pwrmgr,
                 kTestWakeupSources[PWRMGR_PARAM_AON_TIMER_AON_WKUP_REQ_IDX]
                     .wakeup_src)) {
    LOG_INFO("Woke up by source %d", PWRMGR_PARAM_AON_TIMER_AON_WKUP_REQ_IDX);

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
