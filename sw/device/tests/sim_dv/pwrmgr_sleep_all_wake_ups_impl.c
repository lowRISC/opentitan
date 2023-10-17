// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Contains code that is common to deep, normal, and random sleep for
// pwrmgr all_wake_ups test.

#include "sw/device/tests/sim_dv/pwrmgr_sleep_all_wake_ups_impl.h"

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/dif/dif_adc_ctrl.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_sensor_ctrl.h"
#include "sw/device/lib/dif/dif_sysrst_ctrl.h"
#include "sw/device/lib/dif/dif_usbdev.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "pwrmgr_regs.h"
#include "sw/device/lib/testing/autogen/isr_testutils.h"

static const uint32_t kPinmuxWkupDetector5 = 5;

dif_adc_ctrl_t adc_ctrl;
dif_aon_timer_t aon_timer;
dif_pinmux_t pinmux;
dif_pwrmgr_t pwrmgr;
dif_rv_plic_t rv_plic;
dif_sensor_ctrl_t sensor_ctrl;
dif_sysrst_ctrl_t sysrst_ctrl;
dif_usbdev_t usbdev;

/**
 * sysrst_ctrl config for test #1
 * . set sysrst_ctrl.KEY_INTR_CTL.pwrb_in_H2L to 1
 * . use IOR13 as pwrb_in for DV, and IOC0 otherwise
 */
static void prgm_sysrst_ctrl_wakeup(void *dif) {
  dif_sysrst_ctrl_input_change_config_t config = {
      .input_changes = kDifSysrstCtrlInputPowerButtonH2L,
      .debounce_time_threshold = 1,  // 5us
  };
  CHECK_DIF_OK(dif_sysrst_ctrl_input_change_detect_configure(dif, config));
  CHECK_DIF_OK(dif_pinmux_input_select(
      &pinmux, kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonPwrbIn,
      kDeviceType == kDeviceSimDV ? kTopEarlgreyPinmuxInselIor13
                                  : kTopEarlgreyPinmuxInselIoc0));
}

/**
 * adc_ctrl config for test #2
 * . enable filter 5 and set voltage range (0,200)
 */
static void prgm_adc_ctrl_wakeup(void *dif) {
  dif_adc_ctrl_config_t cfg = {
      .mode = kDifAdcCtrlLowPowerScanMode,
      .power_up_time_aon_cycles = 7,
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
 * . use IOB7 as an input for DV, IOC0 otherwise
 * . set posedge detection
 */
static void prgm_pinmux_wakeup(void *dif) {
  // Make sure the pin has a pulldown before we enable it for wakeup.
  // FPGA doesn't implement pullup/down, so just use that attribute for SimDV.
  dif_pinmux_index_t wakeup_pin = kDeviceType == kDeviceSimDV
                                      ? kTopEarlgreyPinmuxInselIob7
                                      : kTopEarlgreyPinmuxInselIoc0;
  dif_pinmux_wakeup_config_t detector_cfg = {
      .signal_filter = kDifToggleDisabled,
      .pad_type = kDifPinmuxPadKindMio,
      .pad_select = wakeup_pin,
      .mode = kDifPinmuxWakeupModePositiveEdge,
      .counter_threshold = 0 /* Don't need for posedge detection */,
  };
  if (kDeviceType != kDeviceSimDV) {
    dif_pinmux_pad_attr_t out_attr;
    dif_pinmux_pad_attr_t in_attr = {
        .slew_rate = 0,
        .drive_strength = 0,
        .flags = kDeviceType == kDeviceSimDV
                     ? kDifPinmuxPadAttrPullResistorEnable
                     : 0};
    CHECK_DIF_OK(dif_pinmux_pad_write_attrs(
        &pinmux, wakeup_pin, kDifPinmuxPadKindMio, in_attr, &out_attr));
  }
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
  dif_usbdev_phy_pins_drive_t pins = {
      .dp_pullup_en = true,
      .dn_pullup_en = false,
  };
  CHECK_DIF_OK(dif_usbdev_set_phy_pins_state(dif, kDifToggleEnabled, pins));
  CHECK_DIF_OK(dif_usbdev_set_wake_enable(dif, kDifToggleEnabled));

  LOG_INFO("prgm_usb_wakeup: wait 20us (usb)");
  // Give the hardware a chance to recognize the wakeup values are the same.
  busy_spin_micros(20);  // 20us
}

/**
 * aon timer config for test #5
 * set wakeup signal in 50us
 */
static void prgm_aontimer_wakeup(void *dif) {
  CHECK_STATUS_OK(aon_timer_testutils_wakeup_config(dif, 10));
}

/**
 * sensor ctrl config for test #6
 * setup event trigger0
 */
static void prgm_sensor_ctrl_wakeup(void *dif) {
  CHECK_DIF_OK(
      dif_sensor_ctrl_set_ast_event_trigger(dif, 0, kDifToggleEnabled));
}

const test_wakeup_sources_t kTestWakeupSources[PWRMGR_PARAM_NUM_WKUPS] = {
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

void init_units(void) {
  CHECK_DIF_OK(dif_adc_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_ADC_CTRL_AON_BASE_ADDR), &adc_ctrl));
  CHECK_DIF_OK(dif_aon_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR), &aon_timer));
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));
  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &rv_plic));
  CHECK_DIF_OK(dif_sysrst_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SYSRST_CTRL_AON_BASE_ADDR),
      &sysrst_ctrl));
  CHECK_DIF_OK(dif_sensor_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SENSOR_CTRL_AON_BASE_ADDR),
      &sensor_ctrl));
  CHECK_DIF_OK(dif_usbdev_init(
      mmio_region_from_addr(TOP_EARLGREY_USBDEV_BASE_ADDR), &usbdev));
}

void execute_test(uint32_t wakeup_source, bool deep_sleep) {
  // Configure wakeup device
  kTestWakeupSources[wakeup_source].config(
      kTestWakeupSources[wakeup_source].dif_handle);
  dif_pwrmgr_domain_config_t cfg;
  CHECK_DIF_OK(dif_pwrmgr_get_domain_config(&pwrmgr, &cfg));
  cfg = (cfg & (kDifPwrmgrDomainOptionIoClockInLowPower |
                kDifPwrmgrDomainOptionUsbClockInLowPower |
                kDifPwrmgrDomainOptionUsbClockInActivePower)) |
        (!deep_sleep ? kDifPwrmgrDomainOptionMainPowerInLowPower : 0);
  CHECK_STATUS_OK(pwrmgr_testutils_enable_low_power(
      &pwrmgr, kTestWakeupSources[wakeup_source].wakeup_src, cfg));
  LOG_INFO("Issue WFI to enter sleep %d", wakeup_source);
  wait_for_interrupt();
}

void check_wakeup_reason(uint32_t wakeup_unit) {
  dif_pwrmgr_wakeup_reason_t wakeup_reason;
  CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_get(&pwrmgr, &wakeup_reason));
  CHECK(UNWRAP(pwrmgr_testutils_is_wakeup_reason(
            &pwrmgr, kTestWakeupSources[wakeup_unit].wakeup_src)) == true,
        "wakeup reason wrong exp:%d  obs:%d",
        kTestWakeupSources[wakeup_unit].wakeup_src, wakeup_reason);
}

static bool get_wakeup_status(void) {
  dif_pwrmgr_request_sources_t wake_req = ~0u;
  CHECK_DIF_OK(dif_pwrmgr_get_current_request_sources(
      &pwrmgr, kDifPwrmgrReqTypeWakeup, &wake_req));
  return (wake_req > 0);
}

void clear_wakeup(uint32_t wakeup_unit) {
  switch (wakeup_unit) {
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
      CHECK_DIF_OK(dif_usbdev_set_wake_enable(&usbdev, kDifToggleDisabled));
      // Write again to make sure the first one has already completed.
      CHECK_DIF_OK(dif_usbdev_set_wake_enable(&usbdev, kDifToggleDisabled));
      CHECK_DIF_OK(dif_pinmux_wakeup_cause_clear(&pinmux));
      break;
    case PWRMGR_PARAM_AON_TIMER_AON_WKUP_REQ_IDX:
      CHECK_DIF_OK(dif_aon_timer_wakeup_stop(&aon_timer));
      // Write again to make sure the first one has already completed.
      CHECK_DIF_OK(dif_aon_timer_wakeup_stop(&aon_timer));
      CHECK_DIF_OK(dif_aon_timer_clear_wakeup_cause(&aon_timer));
      break;
    case PWRMGR_PARAM_SENSOR_CTRL_AON_WKUP_REQ_IDX:
      // clear event trigger
      CHECK_DIF_OK(dif_sensor_ctrl_set_ast_event_trigger(&sensor_ctrl, 0,
                                                         kDifToggleDisabled));
      CHECK_DIF_OK(dif_sensor_ctrl_clear_recov_event(&sensor_ctrl, 0));
      break;
    default:
      LOG_ERROR("unknown wakeup unit %d", wakeup_unit);
  }

  // Ensure the de-asserted events have cleared from the wakeup pipeline
  // within 30us.
  IBEX_SPIN_FOR(!get_wakeup_status(), 100);
  CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_clear(&pwrmgr));
}
static plic_isr_ctx_t plic_ctx = {.rv_plic = &rv_plic,
                                  .hart_id = kTopEarlgreyPlicTargetIbex0};

static pwrmgr_isr_ctx_t pwrmgr_isr_ctx = {
    .pwrmgr = &pwrmgr,
    .plic_pwrmgr_start_irq_id = kTopEarlgreyPlicIrqIdPwrmgrAonWakeup,
    .expected_irq = kDifPwrmgrIrqWakeup,
    .is_only_irq = true};

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
