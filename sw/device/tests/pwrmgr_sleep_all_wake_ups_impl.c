// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Contains code that is common to deep, normal, and random sleep for
// pwrmgr all_wake_ups test.

#include "sw/device/tests/pwrmgr_sleep_all_wake_ups_impl.h"

#include "dt/dt_aon_timer.h"
#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"

#ifdef HAS_ADC_CTRL
#include "dt/dt_adc_ctrl.h"
#include "sw/device/lib/dif/dif_adc_ctrl.h"
#endif
#ifdef HAS_SENSOR_CTRL
#include "dt/dt_sensor_ctrl.h"
#include "sw/device/lib/dif/dif_sensor_ctrl.h"

#include "sensor_ctrl_regs.h"
#endif
#ifdef HAS_SYSRST_CTRL
#include "dt/dt_sysrst_ctrl.h"
#include "sw/device/lib/dif/dif_sysrst_ctrl.h"
#endif
#ifdef HAS_USBDEV
#include "dt/dt_usbdev.h"
#include "sw/device/lib/dif/dif_usbdev.h"
#endif

static const uint32_t kPinmuxWkupDetector5 = 5;
static const uint32_t kSensorCtrlEventIdx = 0;

enum {
  kPlicTarget = 0,
};

static const dt_pwrmgr_t kPwrmgrDt = 0;
static_assert(kDtPwrmgrCount == 1, "this library expects exactly one pwrmgr");
static const dt_pinmux_t kPinmuxDt = 0;
static_assert(kDtPinmuxCount == 1, "this library expects exactly one pinmux");
static const dt_rv_plic_t kRvPlicDt = 0;
static_assert(kDtRvPlicCount == 1, "this library expects exactly one rv_plic");

dif_pwrmgr_t pwrmgr;
dif_rv_plic_t rv_plic;

#define INIT_DIF_DT(__mod_name, __src, __difname)                             \
  dt_##__mod_name##_t __dt = dt_##__mod_name##_from_instance_id(src.inst_id); \
  dif_##__mod_name##_t __difname;                                             \
  CHECK_DIF_OK(dif_##__mod_name##_init_from_dt(__dt, &__difname));

#ifdef HAS_SYSRST_CTRL
/**
 * sysrst_ctrl config for test #1
 * . set sysrst_ctrl.KEY_INTR_CTL.pwrb_in_H2L to 1
 * . use IOR13 as pwrb_in for DV, and IOC0 otherwise
 */
static void sysrst_ctrl_wakeup_config(dt_pwrmgr_wakeup_src_t src) {
  INIT_DIF_DT(sysrst_ctrl, src, sysrst_ctrl)
  dif_sysrst_ctrl_input_change_config_t config = {
      .input_changes = kDifSysrstCtrlInputPowerButtonH2L,
      .debounce_time_threshold = 1,  // 5us
  };
  CHECK_DIF_OK(
      dif_sysrst_ctrl_input_change_detect_configure(&sysrst_ctrl, config));
  dif_pinmux_t pinmux;
  CHECK_DIF_OK(dif_pinmux_init_from_dt(kPinmuxDt, &pinmux));
  CHECK_DIF_OK(dif_pinmux_input_select(
      &pinmux, kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonPwrbIn,
      kDeviceType == kDeviceSimDV ? kTopEarlgreyPinmuxInselIor13
                                  : kTopEarlgreyPinmuxInselIoc0));
}

static void sysrst_ctrl_wakeup_check(dt_pwrmgr_wakeup_src_t src) {
  INIT_DIF_DT(sysrst_ctrl, src, sysrst_ctrl)
  bool has_wakeup = false;
  CHECK_DIF_OK(
      dif_sysrst_ctrl_ulp_wakeup_get_status(&sysrst_ctrl, &has_wakeup));
  CHECK(has_wakeup, "Expected sysrst_ctrl wakeup to be set");
}

static void sysrst_ctrl_wakeup_clear(dt_pwrmgr_wakeup_src_t src) {
  INIT_DIF_DT(sysrst_ctrl, src, sysrst_ctrl)
  CHECK_DIF_OK(dif_sysrst_ctrl_ulp_wakeup_clear_status(&sysrst_ctrl));
  // Disable wakeups.
  dif_sysrst_ctrl_input_change_config_t config = {
      .input_changes = 0,
      .debounce_time_threshold = 0,  // 5us
  };
  CHECK_DIF_OK(
      dif_sysrst_ctrl_input_change_detect_configure(&sysrst_ctrl, config));
}
#endif /* HAS_SYSRST_CTRL */

#ifdef HAS_ADC_CTRL

static bool adc_ctrl_skip(dt_pwrmgr_wakeup_src_t src) {
  return kDeviceType != kDeviceSimDV;
}

/**
 * adc_ctrl config for test #2
 * . enable filter 5 and set voltage range (0,200)
 */
static void adc_ctrl_wakeup_config(dt_pwrmgr_wakeup_src_t src) {
  INIT_DIF_DT(adc_ctrl, src, adc_ctrl)
  dif_adc_ctrl_config_t cfg = {
      .mode = kDifAdcCtrlLowPowerScanMode,
      .power_up_time_aon_cycles = 7,
      .wake_up_time_aon_cycles = 100,
      .num_low_power_samples = 2,
      .num_normal_power_samples = 8,
  };
  CHECK_DIF_OK(dif_adc_ctrl_configure(&adc_ctrl, cfg));

  dif_adc_ctrl_filter_config_t filter_cfg = {
      .filter = kDifAdcCtrlFilter5,
      .min_voltage = 0,
      .max_voltage = 200,
      .in_range = true,
      .generate_wakeup_on_match = true,
      .generate_irq_on_match = false,
  };

  CHECK_DIF_OK(dif_adc_ctrl_configure_filter(&adc_ctrl, kDifAdcCtrlChannel0,
                                             filter_cfg, kDifToggleEnabled));
  CHECK_DIF_OK(dif_adc_ctrl_configure_filter(&adc_ctrl, kDifAdcCtrlChannel1,
                                             filter_cfg, kDifToggleEnabled));
  CHECK_DIF_OK(dif_adc_ctrl_filter_match_wakeup_set_enabled(
      &adc_ctrl, kDifAdcCtrlFilter5, kDifToggleEnabled));
  CHECK_DIF_OK(dif_adc_ctrl_set_enabled(&adc_ctrl, kDifToggleEnabled));
}

static void adc_ctrl_wakeup_check(dt_pwrmgr_wakeup_src_t src) {
  INIT_DIF_DT(adc_ctrl, src, adc_ctrl)
  uint32_t filter_status = 0;
  CHECK_DIF_OK(
      dif_adc_ctrl_wait_cdc_sync(&adc_ctrl, (uint32_t)kClockFreqAonHz));
  CHECK_DIF_OK(dif_adc_ctrl_get_filter_status(&adc_ctrl, &filter_status));
  CHECK(filter_status == ((1 << kDifAdcCtrlFilter5) | (1 << kDifAdcCtrlTrans)),
        "Expected bits %d and %d set in filter status, got status 0x%x",
        kDifAdcCtrlFilter5, kDifAdcCtrlTrans, filter_status);
}

static void adc_ctrl_wakeup_clear(dt_pwrmgr_wakeup_src_t src) {
  INIT_DIF_DT(adc_ctrl, src, adc_ctrl)
  CHECK_DIF_OK(dif_adc_ctrl_filter_match_wakeup_set_enabled(
      &adc_ctrl, kDifAdcCtrlFilter5, kDifToggleDisabled));
}
#endif /* HAS_ADC_CTRL */

/**
 * pinmux config for test #3
 * . use IOB7 as an input for DV, IOC0 otherwise
 * . set posedge detection
 */
static void pinmux_wakeup_config(dt_pwrmgr_wakeup_src_t src) {
  INIT_DIF_DT(pinmux, src, pinmux)
#ifdef OPENTITAN_IS_EARLGREY
  // Make sure the pin has a pulldown before we enable it for wakeup.
  // FPGA doesn't implement pullup/down, so just use that attribute for SimDV.
  dif_pinmux_index_t wakeup_pin = kDeviceType == kDeviceSimDV
                                      ? kTopEarlgreyPinmuxInselIob7
                                      : kTopEarlgreyPinmuxInselIoc0;
#else
#error Unsupported top, please provide a pin configuration
#endif
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
  CHECK_DIF_OK(dif_pinmux_wakeup_detector_enable(&pinmux, kPinmuxWkupDetector5,
                                                 detector_cfg));
}

static void pinmux_wakeup_check(dt_pwrmgr_wakeup_src_t src) {
  INIT_DIF_DT(pinmux, src, pinmux)
  uint32_t wakeup_cause;
  CHECK_DIF_OK(dif_pinmux_wakeup_cause_get(&pinmux, &wakeup_cause));
  CHECK(wakeup_cause == 1 << kPinmuxWkupDetector5,
        "Expected pinmux wakeup cause 5");
}

static void pinmux_wakeup_clear(dt_pwrmgr_wakeup_src_t src) {
  INIT_DIF_DT(pinmux, src, pinmux)
  CHECK_DIF_OK(dif_pinmux_wakeup_cause_clear(&pinmux));
}

#ifdef HAS_USBDEV
/**
 * usb config for test #4
 * . Fake low power entry through usb
 * . Force usb to output suspend indication
 * (*dif) handle is not used but leave as is
 * to be called from execute_test
 */
static void usb_wakeup_config(dt_pwrmgr_wakeup_src_t src) {
  // Despite the name, the wakeup source is the pinmux.
  dif_usbdev_t usbdev;
  static const dt_usbdev_t dt = 0;
  static_assert(kDtUsbdevCount == 1, "expect exactly one usbdev");
  CHECK_DIF_OK(dif_usbdev_init_from_dt(dt, &usbdev));

  dif_usbdev_phy_pins_drive_t pins = {
      .dp_pullup_en = true,
      .dn_pullup_en = false,
  };
  CHECK_DIF_OK(dif_usbdev_set_phy_pins_state(&usbdev, kDifToggleEnabled, pins));
  CHECK_DIF_OK(dif_usbdev_set_wake_enable(&usbdev, kDifToggleEnabled));

  LOG_INFO("usb_wakeup_config: wait 20us (usb)");
  // Give the hardware a chance to recognize the wakeup values are the same.
  busy_spin_micros(20);  // 20us
}

static void usb_wakeup_check(dt_pwrmgr_wakeup_src_t src) {
  // No bit in USBDEV indicates it caused a wakeup.
}

static void usb_wakeup_clear(dt_pwrmgr_wakeup_src_t src) {
  INIT_DIF_DT(pinmux, src, pinmux)
  dif_usbdev_t usbdev;
  static const dt_usbdev_t dt_usbdev = 0;
  static_assert(kDtUsbdevCount == 1, "expect exactly one usbdev");
  CHECK_DIF_OK(dif_usbdev_init_from_dt(dt_usbdev, &usbdev));

  CHECK_DIF_OK(dif_usbdev_set_wake_enable(&usbdev, kDifToggleDisabled));
  // Write again to make sure the first one has already completed.
  CHECK_DIF_OK(dif_usbdev_set_wake_enable(&usbdev, kDifToggleDisabled));
  CHECK_DIF_OK(dif_pinmux_wakeup_cause_clear(&pinmux));
}
#endif /* HAS_USBDEV */

/**
 * aon timer config for test #5
 * set wakeup signal in 50us
 */
static void aontimer_wakeup_config(dt_pwrmgr_wakeup_src_t src) {
  INIT_DIF_DT(aon_timer, src, aon_timer)
  CHECK_STATUS_OK(aon_timer_testutils_wakeup_config(&aon_timer, 10));
}

static void aontimer_wakeup_check(dt_pwrmgr_wakeup_src_t src) {
  INIT_DIF_DT(aon_timer, src, aon_timer)
  bool cause = false;
  CHECK_DIF_OK(dif_aon_timer_get_wakeup_cause(&aon_timer, &cause));
  CHECK(cause, "Expected aontimer wakeup cause to be enabled");
}

static void aontimer_wakeup_clear(dt_pwrmgr_wakeup_src_t src) {
  INIT_DIF_DT(aon_timer, src, aon_timer)
  CHECK_DIF_OK(dif_aon_timer_wakeup_stop(&aon_timer));
  // Write again to make sure the first one has already completed.
  CHECK_DIF_OK(dif_aon_timer_wakeup_stop(&aon_timer));
  CHECK_DIF_OK(dif_aon_timer_clear_wakeup_cause(&aon_timer));
}

#ifdef HAS_SENSOR_CTRL
/**
 * sensor ctrl config for test #6
 * setup event trigger0
 */
static void sensor_ctrl_wakeup_config(dt_pwrmgr_wakeup_src_t src) {
  INIT_DIF_DT(sensor_ctrl, src, sensor_ctrl)
  // Enable all AST alerts in sensor_ctrl
  for (uint32_t k = 0; k < SENSOR_CTRL_PARAM_NUM_ALERT_EVENTS; k++) {
    CHECK_DIF_OK(
        dif_sensor_ctrl_set_alert_en(&sensor_ctrl, k, kDifToggleEnabled));
  }
  CHECK_DIF_OK(dif_sensor_ctrl_set_ast_event_trigger(
      &sensor_ctrl, kSensorCtrlEventIdx, kDifToggleEnabled));
}

static void sensor_ctrl_wakeup_check(dt_pwrmgr_wakeup_src_t src) {
  INIT_DIF_DT(sensor_ctrl, src, sensor_ctrl)
  dif_sensor_ctrl_events_t events;
  dif_toggle_t enable;
  CHECK_DIF_OK(dif_sensor_ctrl_get_ast_event_trigger(
      &sensor_ctrl, kSensorCtrlEventIdx, &enable));
  CHECK(enable == kDifToggleEnabled, "Expected event trigger enabled");
  CHECK_DIF_OK(dif_sensor_ctrl_get_recov_events(&sensor_ctrl, &events));
  CHECK(events & (1 << kSensorCtrlEventIdx), "Expected bit %d to be set",
        kSensorCtrlEventIdx);
}

static void sensor_ctrl_wakeup_clear(dt_pwrmgr_wakeup_src_t src) {
  INIT_DIF_DT(sensor_ctrl, src, sensor_ctrl)
  // clear event trigger
  CHECK_DIF_OK(dif_sensor_ctrl_set_ast_event_trigger(
      &sensor_ctrl, kSensorCtrlEventIdx, kDifToggleDisabled));
  CHECK_DIF_OK(
      dif_sensor_ctrl_clear_recov_event(&sensor_ctrl, kSensorCtrlEventIdx));
  dif_toggle_t enable;
  CHECK_DIF_OK(dif_sensor_ctrl_get_ast_event_trigger(
      &sensor_ctrl, kSensorCtrlEventIdx, &enable));
  CHECK(enable == kDifToggleDisabled, "Expected event trigger disabled");
  dif_sensor_ctrl_events_t events;
  CHECK_DIF_OK(dif_sensor_ctrl_get_recov_events(&sensor_ctrl, &events));
  CHECK(events == 0, "Expected recoverable events to be clear, got 0x%x",
        events);
}
#endif /* HAS_SENSOR_CTRL */

const test_wakeup_sources_t kTestWakeupSources[] = {
#ifdef HAS_SYSRST_CTRL
    {
        .name = "SYSRST_CTRL",
        .dev_type = kDtDeviceTypeSysrstCtrl,
        .wakeup = kDtSysrstCtrlWakeupWkupReq,
        .skip = NULL,
        .config = sysrst_ctrl_wakeup_config,
        .check = sysrst_ctrl_wakeup_check,
        .clear = sysrst_ctrl_wakeup_clear,
    },
#endif /* HAS_SYSRST_CTRL */
#ifdef HAS_ADC_CTRL
    {
        .name = "ADC_CTRL",
        .dev_type = kDtDeviceTypeAdcCtrl,
        .wakeup = kDtAdcCtrlWakeupWkupReq,
        .skip = adc_ctrl_skip,
        .config = adc_ctrl_wakeup_config,
        .check = adc_ctrl_wakeup_check,
        .clear = adc_ctrl_wakeup_clear,
    },
#endif /* HAS_ADC_CTRL */
    {
        .name = "PINMUX",
        .dev_type = kDtDeviceTypePinmux,
        .wakeup = kDtPinmuxWakeupPinWkupReq,
        .skip = NULL,
        .config = pinmux_wakeup_config,
        .check = pinmux_wakeup_check,
        .clear = pinmux_wakeup_clear,
    },
#ifdef HAS_USBDEV
    {
        .name = "USB",
        .dev_type = kDtDeviceTypePinmux,
        .wakeup = kDtPinmuxWakeupUsbWkupReq,
        .skip = NULL,
        .config = usb_wakeup_config,
        .check = usb_wakeup_check,
        .clear = usb_wakeup_clear,
    },
#endif /* HAS_USBDEV */
    {
        .name = "AONTIMER",
        .dev_type = kDtDeviceTypeAonTimer,
        .wakeup = kDtAonTimerWakeupWkupReq,
        .skip = NULL,
        .config = aontimer_wakeup_config,
        .check = aontimer_wakeup_check,
        .clear = aontimer_wakeup_clear,
    },
#ifdef HAS_SENSOR_CTRL
    {
        .name = "SENSOR_CTRL",
        .dev_type = kDtDeviceTypeSensorCtrl,
        .wakeup = kDtSensorCtrlWakeupWkupReq,
        .skip = NULL,
        .config = sensor_ctrl_wakeup_config,
        .check = sensor_ctrl_wakeup_check,
        .clear = sensor_ctrl_wakeup_clear,
    },
#endif /* HAS_SENSOR_CTRL */
};

const test_wakeup_sources_t *get_wakeup_source(
    size_t wakeup_unit, dt_pwrmgr_wakeup_src_t *out_src) {
  dt_pwrmgr_wakeup_src_t src = dt_pwrmgr_wakeup_src(kPwrmgrDt, wakeup_unit);
  if (out_src) {
    *out_src = src;
  }
  for (size_t idx = 0; idx < ARRAYSIZE(kTestWakeupSources); idx++) {
    if (dt_device_type(src.inst_id) == kTestWakeupSources[idx].dev_type &&
        src.wakeup == kTestWakeupSources[idx].wakeup) {
      return &kTestWakeupSources[idx];
    }
  }
  LOG_ERROR("unable to test wakeup source %d (inst_id=%d, wkup=%d)",
            wakeup_unit, src.inst_id, src.wakeup);
  return NULL;
}

void init_units(void) {
  CHECK_DIF_OK(dif_pwrmgr_init_from_dt(kPwrmgrDt, &pwrmgr));
  CHECK_DIF_OK(dif_rv_plic_init_from_dt(kRvPlicDt, &rv_plic));
  // Enable all the AON interrupts used in this test.
  dif_rv_plic_irq_id_t irq_id =
      dt_pwrmgr_irq_to_plic_id(kPwrmgrDt, kDtPwrmgrIrqWakeup);
  rv_plic_testutils_irq_range_enable(&rv_plic, kPlicTarget, irq_id, irq_id);
  // Enable pwrmgr interrupt
  CHECK_DIF_OK(dif_pwrmgr_irq_set_enabled(&pwrmgr, 0, kDifToggleEnabled));
}

size_t get_wakeup_count(void) { return dt_pwrmgr_wakeup_src_count(kPwrmgrDt); }

bool execute_test(size_t wakeup_unit, bool deep_sleep) {
  dt_pwrmgr_wakeup_src_t wakeup;
  const test_wakeup_sources_t *src = get_wakeup_source(wakeup_unit, &wakeup);
  CHECK(src, "cannot execute test");

  if (src->skip && src->skip(wakeup)) {
    LOG_INFO("Skip %d (%s)", wakeup_unit, src->name);
    return false;
  }

  // This message is used by the harness to know how to wakeup the device.
  LOG_INFO("Test %d begin (%s)", wakeup_unit, src->name);

  // Configure wakeup device
  src->config(wakeup);
  dif_pwrmgr_domain_config_t cfg;
  CHECK_DIF_OK(dif_pwrmgr_get_domain_config(&pwrmgr, &cfg));
  if (deep_sleep) {
    cfg &= ~kDifPwrmgrDomainOptionMainPowerInLowPower;
  } else {
    cfg |= kDifPwrmgrDomainOptionMainPowerInLowPower;
  }
  CHECK_STATUS_OK(
      pwrmgr_testutils_enable_low_power(&pwrmgr, 1 << wakeup_unit, cfg));
  LOG_INFO("Issue WFI to enter sleep %d", wakeup_unit);
  wait_for_interrupt();
  return true;
}

void check_wakeup_reason(size_t wakeup_unit) {
  dt_pwrmgr_wakeup_src_t wakeup;
  const test_wakeup_sources_t *src = get_wakeup_source(wakeup_unit, &wakeup);
  CHECK(src, "cannot execute test");

  dif_pwrmgr_wakeup_reason_t wakeup_reason;
  CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_get(&pwrmgr, &wakeup_reason));
  CHECK(UNWRAP(pwrmgr_testutils_is_wakeup_reason(&pwrmgr, 1 << wakeup_unit)),
        "wakeup reason wrong exp:%x  obs:%x", wakeup_unit, wakeup_reason);

  src->check(wakeup);
}

static bool get_wakeup_status(void) {
  dif_pwrmgr_request_sources_t wake_req = ~0u;
  CHECK_DIF_OK(dif_pwrmgr_get_current_request_sources(
      &pwrmgr, kDifPwrmgrReqTypeWakeup, &wake_req));
  return (wake_req > 0);
}

void clear_wakeup(size_t wakeup_unit) {
  dt_pwrmgr_wakeup_src_t wakeup;
  const test_wakeup_sources_t *src = get_wakeup_source(wakeup_unit, &wakeup);
  CHECK(src, "cannot execute test");

  src->clear(wakeup);
  // Ensure the de-asserted events have cleared from the wakeup pipeline
  // within 100us.
  IBEX_SPIN_FOR(!get_wakeup_status(), 100);
  CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_clear(&pwrmgr));
}

/**
 * External interrupt handler.
 */
bool ottf_handle_irq(uint32_t *exc_info, dt_instance_id_t devid,
                     dif_rv_plic_irq_id_t irq_id) {
  if (devid == dt_pwrmgr_instance_id(kPwrmgrDt) &&
      irq_id == dt_pwrmgr_irq_to_plic_id(kPwrmgrDt, kDtPwrmgrIrqWakeup)) {
    CHECK_DIF_OK(dif_pwrmgr_irq_acknowledge(&pwrmgr, kDtPwrmgrIrqWakeup));
    return true;
  } else {
    return false;
  }
}
