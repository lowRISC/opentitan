// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rand_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "pinmux_regs.h"  // Generated.
#include "sw/device/lib/testing/autogen/isr_testutils.h"

OTTF_DEFINE_TEST_CONFIG();

// PLIC structures
static dif_pwrmgr_t pwrmgr;
static dif_pinmux_t pinmux;
static dif_rv_plic_t plic;

static const uint32_t kNumDio = 16;  // top_earlgrey has 16 DIOs

// kDirectDio is a list of Dio index that TB cannot control the PAD value.
// The list should be incremental order (see the code below)
#define NUM_DIRECT_DIO 5
static const uint32_t kDirectDio[NUM_DIRECT_DIO] = {6, 12, 13, 14, 15};

static plic_isr_ctx_t plic_ctx = {.rv_plic = &plic,
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

bool test_main(void) {
  dif_pinmux_wakeup_config_t wakeup_cfg;

  // Default Deep Power Down
  dif_pwrmgr_domain_config_t pwrmgr_domain_cfg = 0;

  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  // Initialize power manager
  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));
  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &plic));
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));

  // Randomly pick one of the wakeup detectors.
  dif_pinmux_index_t wakeup_detector_selected =
      rand_testutils_gen32_range(0, PINMUX_PARAM_N_WKUP_DETECT - 1);

  if (UNWRAP(pwrmgr_testutils_is_wakeup_reason(&pwrmgr, 0)) == true) {
    LOG_INFO("Test in POR phase");

    LOG_INFO("pinmux_init end");

    // TODO(lowrisc/opentitan#15889): The weak pull on IOC3 needs to be
    // disabled for this test. Remove this later.
    dif_pinmux_pad_attr_t out_attr;
    dif_pinmux_pad_attr_t in_attr = {0};
    CHECK_DIF_OK(dif_pinmux_pad_write_attrs(&pinmux, kTopEarlgreyMuxedPadsIoc3,
                                            kDifPinmuxPadKindMio, in_attr,
                                            &out_attr));

    // Random choose low power or deep powerdown
    uint32_t deep_powerdown_en = rand_testutils_gen32_range(0, 1);

    // Prepare which PAD SW want to select
    uint32_t mio0_dio1 = rand_testutils_gen32_range(0, 1);
    uint32_t pad_sel = 0;

    // Enable AonWakeup Interrupt if normal sleep
    if (deep_powerdown_en == 0) {
      // Enable all the AON interrupts used in this test.
      rv_plic_testutils_irq_range_enable(&plic, kTopEarlgreyPlicTargetIbex0,
                                         kTopEarlgreyPlicIrqIdPwrmgrAonWakeup,
                                         kTopEarlgreyPlicIrqIdPwrmgrAonWakeup);
      // Enable pwrmgr interrupt
      CHECK_DIF_OK(dif_pwrmgr_irq_set_enabled(&pwrmgr, 0, kDifToggleEnabled));
    }

    // SpiDev CLK(idx 12), CS#(idx 13), D0(idx 6) and SpiHost CLK (14), CS#
    // (15) are directly connected to the SPI IF. Cannot control them. Roll 3
    // less and compensated later.
    if (mio0_dio1) {
      // DIO
      pad_sel = rand_testutils_gen32_range(0, kNumDio - 1 - NUM_DIRECT_DIO);

      for (int i = 0; i < NUM_DIRECT_DIO; i++) {
        if (pad_sel >= kDirectDio[i]) {
          pad_sel++;
        }
      }
      LOG_INFO("Pad Selection: %d / %d", mio0_dio1, pad_sel);
    } else {
      // MIO: 0, 1 are tie-0, tie-1
      pad_sel = rand_testutils_gen32_range(2, kTopEarlgreyPinmuxInselLast);
      LOG_INFO("Pad Selection: %d / %d", mio0_dio1, pad_sel - 2);
    }

    if (mio0_dio1 == 0) {
      // TODO: Check if the PAD is locked (kDifPinmuxLockTargetOutsel), then
      // skip if locked.
      // Turn off Pinmux output selection
      CHECK_DIF_OK(dif_pinmux_output_select(
          &pinmux, pad_sel - 2, kTopEarlgreyPinmuxOutselConstantHighZ));
    }

    wakeup_cfg.mode = kDifPinmuxWakeupModePositiveEdge;
    wakeup_cfg.signal_filter = false;
    wakeup_cfg.pad_type = mio0_dio1;
    wakeup_cfg.pad_select = pad_sel;

    // TODO: A better test would be to program ALL wakeup detectors with
    // randomly chosen pin wakeup sources and prove the right wakeup source
    // woke up the chip from sleep.
    CHECK_DIF_OK(dif_pinmux_wakeup_detector_enable(
        &pinmux, wakeup_detector_selected, wakeup_cfg));

    if (deep_powerdown_en == 0) {
      pwrmgr_domain_cfg = kDifPwrmgrDomainOptionMainPowerInLowPower |
                          kDifPwrmgrDomainOptionUsbClockInActivePower;
    }
    // Enter low power
    CHECK_STATUS_OK(pwrmgr_testutils_enable_low_power(
        &pwrmgr, kDifPwrmgrWakeupRequestSourceThree, pwrmgr_domain_cfg));

    LOG_INFO("Entering low power mode.");
    wait_for_interrupt();
  }

  if (UNWRAP(pwrmgr_testutils_is_wakeup_reason(
          &pwrmgr, kDifPwrmgrWakeupRequestSourceThree)) == true) {
    LOG_INFO("Test in post-sleep pin wakeup phase");
    uint32_t wakeup_cause;
    CHECK_DIF_OK(dif_pinmux_wakeup_cause_get(&pinmux, &wakeup_cause));
    CHECK(wakeup_cause == 1 << wakeup_detector_selected);
    CHECK_DIF_OK(
        dif_pinmux_wakeup_detector_disable(&pinmux, wakeup_detector_selected));
    return true;

  } else {
    // Other wakeup. This is a failure.
    dif_pwrmgr_wakeup_reason_t wakeup_reason;
    CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_get(&pwrmgr, &wakeup_reason));
    LOG_ERROR("Unexpected wakeup detected: type = %d, request_source = %d",
              wakeup_reason.types, wakeup_reason.request_sources);
    return false;
  }

  return false;
}

#undef NUM_DIRECT_DIO
#undef NUM_LOCKED_MIO
