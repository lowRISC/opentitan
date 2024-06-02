// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_adc_ctrl.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_sensor_ctrl.h"
#include "sw/device/lib/dif/dif_sysrst_ctrl.h"
#include "sw/device/lib/dif/dif_usbdev.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "pinmux_regs.h"
#include "pwrmgr_regs.h"
#include "sw/device/lib/testing/autogen/isr_testutils.h"

dif_pinmux_t pinmux;
dif_pwrmgr_t pwrmgr;
dif_rv_plic_t rv_plic;

static dif_pwrmgr_request_sources_t wakeup_src =
    kDifPwrmgrWakeupRequestSourceThree;
static uint32_t wakeup_source = PWRMGR_PARAM_PINMUX_AON_PIN_WKUP_REQ_IDX;
static const uint32_t kPinmuxWkupDetector5 = 5;

static plic_isr_ctx_t plic_ctx = {.rv_plic = &rv_plic,
                                  .hart_id = kTopEarlgreyPlicTargetIbex0};

static pwrmgr_isr_ctx_t pwrmgr_isr_ctx = {
    .pwrmgr = &pwrmgr,
    .plic_pwrmgr_start_irq_id = kTopEarlgreyPlicIrqIdPwrmgrAonWakeup,
    .expected_irq = kDifPwrmgrIrqWakeup,
    .is_only_irq = true};

static dif_rv_timer_t timer;
static volatile bool irq_fired = true;
static const uint32_t kHart = (uint32_t)kTopEarlgreyPlicTargetIbex0;
static const uint32_t kComparator = 0;
static const uint64_t kTickFreqHz = 1000 * 1000;  // 1 MHz.

void ottf_external_isr(uint32_t *exc_info) {
  dif_pwrmgr_irq_t irq_id;
  top_earlgrey_plic_peripheral_t peripheral;

  isr_testutils_pwrmgr_isr(plic_ctx, pwrmgr_isr_ctx, &peripheral, &irq_id);

  // Check that both the peripheral and the irq id is correct
  CHECK(peripheral == kTopEarlgreyPlicPeripheralPwrmgrAon,
        "IRQ peripheral: %d is incorrect", peripheral);
  CHECK(irq_id == kDifPwrmgrIrqWakeup, "IRQ ID: %d is incorrect", irq_id);
}

void ottf_timer_isr(uint32_t *exc_info) {
  CHECK(!irq_fired, "Entered IRQ handler, but `irq_fired` was not false!");

  bool irq_flag;
  CHECK_DIF_OK(dif_rv_timer_irq_is_pending(
      &timer, kDifRvTimerIrqTimerExpiredHart0Timer0, &irq_flag));
  CHECK(irq_flag, "Entered IRQ handler but the expected IRQ flag wasn't set!");

  CHECK_DIF_OK(
      dif_rv_timer_counter_set_enabled(&timer, kHart, kDifToggleDisabled));
  CHECK_DIF_OK(dif_rv_timer_irq_acknowledge(
      &timer, kDifRvTimerIrqTimerExpiredHart0Timer0));

  irq_fired = true;
  LOG_INFO("Timer ISR");
}

static void prgm_pinmux_wakeup(void) {
  // Use IOB7 as an input for DV, IOC0 otherwise.
  // Set posedge detection.
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
  CHECK_DIF_OK(dif_pinmux_wakeup_detector_enable(&pinmux, kPinmuxWkupDetector5,
                                                 detector_cfg));
}

static bool get_wakeup_status(void) {
  dif_pwrmgr_request_sources_t wake_req = ~0u;
  CHECK_DIF_OK(dif_pwrmgr_get_current_request_sources(
      &pwrmgr, kDifPwrmgrReqTypeWakeup, &wake_req));
  return (wake_req > 0);
}

static void clear_wakeup(void) {
  CHECK_DIF_OK(dif_pinmux_wakeup_cause_clear(&pinmux));
  // Ensure the de-asserted events have cleared from the wakeup pipeline
  // within 100us.
  IBEX_SPIN_FOR(!get_wakeup_status(), 100);
  CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_clear(&pwrmgr));
}

static void sync_slow_clock_domain_polled(const dif_pwrmgr_t *pwrmgr) {
  mmio_region_write32(
      pwrmgr->base_addr, PWRMGR_CFG_CDC_SYNC_REG_OFFSET,
      bitfield_bit32_write(0, PWRMGR_CFG_CDC_SYNC_SYNC_BIT, true));
  while (bitfield_bit32_read(
      mmio_region_read32(pwrmgr->base_addr, PWRMGR_CFG_CDC_SYNC_REG_OFFSET),
      PWRMGR_CFG_CDC_SYNC_SYNC_BIT)) {
  }
}

static void test_init(void) {
  irq_global_ctrl(true);
  irq_external_ctrl(true);
  irq_timer_ctrl(true);

  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));
  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &rv_plic));

  // Enable AON interrupts.
  rv_plic_testutils_irq_range_enable(&rv_plic, kTopEarlgreyPlicTargetIbex0,
                                     kTopEarlgreyPlicIrqIdPwrmgrAonWakeup,
                                     kTopEarlgreyPlicIrqIdPwrmgrAonWakeup);
  // Enable pwrmgr interrupt
  CHECK_DIF_OK(dif_pwrmgr_irq_set_enabled(&pwrmgr, 0, kDifToggleEnabled));

  CHECK_DIF_OK(dif_rv_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_TIMER_BASE_ADDR), &timer));
  CHECK_DIF_OK(dif_rv_timer_reset(&timer));
  dif_rv_timer_tick_params_t tick_params;
  CHECK_DIF_OK(dif_rv_timer_approximate_tick_params(kClockFreqPeripheralHz,
                                                    kTickFreqHz, &tick_params));
  CHECK_DIF_OK(dif_rv_timer_set_tick_params(&timer, kHart, tick_params));
  CHECK_DIF_OK(dif_rv_timer_irq_set_enabled(
      &timer, kDifRvTimerIrqTimerExpiredHart0Timer0, kDifToggleEnabled));

  prgm_pinmux_wakeup();
}

static void set_timer(uint64_t time) {
  uint64_t current_time;
  CHECK_DIF_OK(dif_rv_timer_counter_read(&timer, kHart, &current_time));
  CHECK_DIF_OK(
      dif_rv_timer_arm(&timer, kHart, kComparator, current_time + time));
  irq_fired = false;
  CHECK_DIF_OK(
      dif_rv_timer_counter_set_enabled(&timer, kHart, kDifToggleEnabled));
}

static void test_sleep(bool wfi_fallthrough) {
  LOG_INFO("Low power WFI (fallthrough=%d)", wfi_fallthrough);
  mmio_region_write32(pwrmgr.base_addr, PWRMGR_WAKEUP_EN_REG_OFFSET,
                      wakeup_src);
  mmio_region_write32(pwrmgr.base_addr, PWRMGR_CONTROL_REG_OFFSET,
                      (1 << PWRMGR_CONTROL_MAIN_PD_N_BIT) |
                          (1 << PWRMGR_CONTROL_LOW_POWER_HINT_BIT));
  sync_slow_clock_domain_polled(&pwrmgr);
  LOG_INFO("CONTROL=0x%x",
           mmio_region_read32(pwrmgr.base_addr, PWRMGR_CONTROL_REG_OFFSET));
  irq_global_ctrl(false);
  if (wfi_fallthrough) {
    LOG_INFO("Fallthough WFI due to timer pending");
    set_timer(100);
    busy_spin_micros(200);
  } else {
    // This log message causes the edge from hyperdebug to wake us up.
    LOG_INFO("Issue WFI to enter sleep %d", wakeup_source);
  }
  wait_for_interrupt();
  irq_global_ctrl(true);
  LOG_INFO("CONTROL=0x%x",
           mmio_region_read32(pwrmgr.base_addr, PWRMGR_CONTROL_REG_OFFSET));
  LOG_INFO("WAKE_INFO=0x%x",
           mmio_region_read32(pwrmgr.base_addr, PWRMGR_WAKE_INFO_REG_OFFSET));
  LOG_INFO("WKUP_CAUSE=0x%x",
           mmio_region_read32(pinmux.base_addr, PINMUX_WKUP_CAUSE_REG_OFFSET));
  LOG_INFO("Woke up by source %d", wakeup_source);
  clear_wakeup();

  LOG_INFO("Normal WFI");
  // This should clear LOW_POWER_HINT_BIT, but it doesn't.
  mmio_region_write32(pwrmgr.base_addr, PWRMGR_CONTROL_REG_OFFSET,
                      (1 << PWRMGR_CONTROL_MAIN_PD_N_BIT));
  sync_slow_clock_domain_polled(&pwrmgr);
  LOG_INFO("CONTROL=0x%x",
           mmio_region_read32(pwrmgr.base_addr, PWRMGR_CONTROL_REG_OFFSET));
  set_timer(500);
  wait_for_interrupt();
  LOG_INFO("CONTROL=0x%x",
           mmio_region_read32(pwrmgr.base_addr, PWRMGR_CONTROL_REG_OFFSET));
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  test_init();
  if (UNWRAP(pwrmgr_testutils_is_wakeup_reason(&pwrmgr, 0)) != true) {
    return false;
  }
  test_sleep(false);
  test_sleep(true);
  return true;
}
