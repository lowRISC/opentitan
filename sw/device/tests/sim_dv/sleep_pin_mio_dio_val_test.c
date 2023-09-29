// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/ip/pinmux/dif/dif_pinmux.h"
#include "sw/ip/pwrmgr/dif/dif_pwrmgr.h"
#include "sw/ip/pwrmgr/test/utils/pwrmgr_testutils.h"
#include "sw/ip/rv_core_ibex/test/utils/rand_testutils.h"
#include "sw/ip/rv_plic/dif/dif_rv_plic.h"
#include "sw/ip/rv_plic/test/utils/rv_plic_testutils.h"
#include "sw/lib/sw/device/base/mmio.h"
#include "sw/lib/sw/device/runtime/irq.h"
#include "sw/lib/sw/device/runtime/log.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"
#include "sw/top_darjeeling/sw/test/utils/autogen/isr_testutils.h"

OTTF_DEFINE_TEST_CONFIG();

/**
 * Test: chip_sw_sleep_pin_mio_dio_val
 *
 * chip_sw_sleep_pin_mio_dio_val test is to check the PADs assert desired
 * values. When the chip enters deep powerdown (turning off power domains
 * except AON), PADs cannot get the data from off domain logics.
 *
 * To not confuse the devices outside of the logic, usually isolation cells are
 * placed in between (off and on). OpenTitan, on top of the isolation, provides
 * a functionality to control the PADs output value among **0**, **1**,
 * **High-Z**, and **Passthrough**. Refer the PINMUX technical specification
 * for the details.
 *
 * In this test, the code randomizes the output values except the
 * **passthrough**, as **passthrough** is tested in other chip level test. Then
 * the chosen values are given to the UVM testbenches. UVM testbenches compare
 * the expected and measured values.
 */

/**
 * If certain DIOs need to be skipped due to tied functionality, specify here.
 */
enum { kNumOptOutDio = 0 };
static const uint8_t kOptOutDio[1] = {0};

enum { kNumOptOutMio = 0 };

static uint8_t kMioPads[TOP_DARJEELING_NUM_MIO_PADS] = {0};
static uint8_t kDioPads[TOP_DARJEELING_NUM_DIO_PADS] = {0};

// PLIC structures
static dif_pwrmgr_t pwrmgr;
static dif_pinmux_t pinmux;
static dif_rv_plic_t plic;

static plic_isr_ctx_t plic_ctx = {.rv_plic = &plic,
                                  .hart_id = kTopDarjeelingPlicTargetIbex0};

static pwrmgr_isr_ctx_t pwrmgr_isr_ctx = {
    .pwrmgr = &pwrmgr,
    .plic_pwrmgr_start_irq_id = kTopDarjeelingPlicIrqIdPwrmgrAonWakeup,
    .expected_irq = kDifPwrmgrIrqWakeup,
    .is_only_irq = true};

/**
 * External interrupt handler.
 */
void ottf_external_isr(void) {
  dif_pwrmgr_irq_t irq_id;
  top_darjeeling_plic_peripheral_t peripheral;

  isr_testutils_pwrmgr_isr(plic_ctx, pwrmgr_isr_ctx, &peripheral, &irq_id);

  // Check that both the peripheral and the irq id is correct
  CHECK(peripheral == kTopDarjeelingPlicPeripheralPwrmgrAon,
        "IRQ peripheral: %d is incorrect", peripheral);
  CHECK(irq_id == kDifPwrmgrIrqWakeup, "IRQ ID: %d is incorrect", irq_id);
}

/** Configure pinmux retention value.
 *
 * Each gen32 can cover 16 PADs randomization. When each pad ret val draws
 * **3**, the code calls gen32_range to choose from 0 to 2.
 */
void draw_pinmux_ret(const uint32_t num_pins, uint8_t *arr,
                     const uint8_t *optout, const uint8_t num_optout) {
  for (uint32_t i = 0; i < num_pins; i += 16) {
    uint32_t val = rand_testutils_gen32();
    uint32_t min_idx = (i + 16 < num_pins) ? i + 16 : num_pins;

    for (uint32_t j = i; j < min_idx; j++) {
      /* Bit slice 2b at a time and if it is 3, redraw */
      arr[j] = (val >> ((j & 0xF) * 2)) & 0x3;
      if (arr[j] == 3) {
        arr[j] = (uint8_t)rand_testutils_gen32_range(0, 2);
      }
    }
  }

  // OptOut processing after draw.
  for (int i = 0; i < num_optout; i++) {
    CHECK(optout != NULL, "optout must be non-NULL");
    arr[optout[i]] = 2;  // High-Z always
  }
}

/**
 * Send the chosen values to UVM tb.
 *
 * Format:
 *
 *     "{DIO/MIO} [i]: {}"
 */
void print_chosen_values(void) {
  LOG_INFO("BEGIN Chosen Retention Types");
  for (int i = 0; i < TOP_DARJEELING_NUM_MIO_PADS; ++i) {
    LOG_INFO("MIO [%d]: %x", i, kMioPads[i]);
  }
  for (int i = 0; i < TOP_DARJEELING_NUM_DIO_PADS; ++i) {
    LOG_INFO("DIO [%d]: %x", i, kDioPads[i]);
  }
  LOG_INFO("END Chosen Retention Types");
}

/**
 * Configure PADs retention types.
 *
 * @param pinmux Pinmux handle.
 */
void configure_pad_retention_types(dif_pinmux_t *pinmux) {
  uint8_t io;  // 1 for DIO, 0 for MIO
  uint32_t max_pads;
  dif_pinmux_pad_kind_t pad_kind;
  dif_pinmux_sleep_mode_t pad_mode;
  LOG_INFO("Configuring PADs retention types in PINMUX...");

  // TODO: for loop of writing values to PINMUX CSRs.
  for (io = 0; io < 2; io++) {
    max_pads = (io) ? TOP_DARJEELING_NUM_DIO_PADS : TOP_DARJEELING_NUM_MIO_PADS;
    pad_kind = (io) ? kDifPinmuxPadKindDio : kDifPinmuxPadKindMio;
    for (int i = 0; i < max_pads; i++) {
      pad_mode = (io) ? (dif_pinmux_sleep_mode_t)(kDioPads[i])
                      : (dif_pinmux_sleep_mode_t)(kMioPads[i]);
      CHECK_DIF_OK(dif_pinmux_pad_sleep_enable(pinmux, (dif_pinmux_index_t)i,
                                               pad_kind, pad_mode));
    }
  }

  LOG_INFO("PADs retention modes are configured.");
}

bool lowpower_prep(dif_pwrmgr_t *pwrmgr, dif_pinmux_t *pinmux, bool deepsleep) {
  bool result = false;
  dif_pwrmgr_domain_config_t pwrmgr_domain_cfg = 0;

  LOG_INFO("Selecting PADs retention modes...");

  draw_pinmux_ret(TOP_DARJEELING_NUM_DIO_PADS, kDioPads, kOptOutDio,
                  kNumOptOutDio);
  draw_pinmux_ret(TOP_DARJEELING_NUM_MIO_PADS, kMioPads, NULL, kNumOptOutMio);

  print_chosen_values();

  // Configure pwrmgr to deep powerdown.
  configure_pad_retention_types(pinmux);

  if (!deepsleep) {
    pwrmgr_domain_cfg = kDifPwrmgrDomainOptionMainPowerInLowPower |
                        kDifPwrmgrDomainOptionUsbClockInActivePower;
  }
  CHECK_DIF_OK(dif_pwrmgr_set_domain_config(pwrmgr, pwrmgr_domain_cfg,
                                            kDifToggleEnabled));
  CHECK_DIF_OK(dif_pwrmgr_low_power_set_enabled(pwrmgr, kDifToggleEnabled,
                                                kDifToggleEnabled));

  wait_for_interrupt();  // Entering deep power down.

  return result;
}

bool test_main(void) {
  bool result = false;

  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_DARJEELING_PWRMGR_AON_BASE_ADDR), &pwrmgr));
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_DARJEELING_PINMUX_AON_BASE_ADDR), &pinmux));
  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_DARJEELING_RV_PLIC_BASE_ADDR), &plic));

  if (UNWRAP(pwrmgr_testutils_is_wakeup_reason(&pwrmgr, 0)) == true) {
    uint32_t deep_powerdown_en = rand_testutils_gen32_range(0, 1);
    bool deepsleep = (deep_powerdown_en) ? true : false;

    if (!deepsleep) {
      // Enable all the AON interrupts used in this test.
      rv_plic_testutils_irq_range_enable(
          &plic, kTopDarjeelingPlicTargetIbex0,
          kTopDarjeelingPlicIrqIdPwrmgrAonWakeup,
          kTopDarjeelingPlicIrqIdPwrmgrAonWakeup);
      // Enable pwrmgr interrupt
      CHECK_DIF_OK(dif_pwrmgr_irq_set_enabled(&pwrmgr, 0, kDifToggleEnabled));
    }

    result = lowpower_prep(&pwrmgr, &pinmux, deepsleep);
  }

  if (UNWRAP(pwrmgr_testutils_is_wakeup_reason(
          &pwrmgr, kDifPwrmgrWakeupRequestSourceThree)) == true) {
    // TODO: change PINMUX wakeup, not pin detector
    /**
     *  Usually this part won't be hit. UVM testbench checks the PAD output
     *  values and raises an error if failed.
     */
  } else {
    // Other wakeup. This is a failure.
    dif_pwrmgr_wakeup_reason_t wakeup_reason;
    CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_get(&pwrmgr, &wakeup_reason));
    LOG_ERROR("Unexpected wakeup detected: type = %d, request_source = %d",
              wakeup_reason.types, wakeup_reason.request_sources);
    result = false;
  }

  return result;
}
