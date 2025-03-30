// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

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

#if defined(OPENTITAN_IS_EARLGREY)
static const dt_pad_t kOptOut[] = {
    kDtPadSpiDeviceSck,
    kDtPadSpiDeviceCsb,
};
#elif defined(OPENTITAN_IS_DARJEELING)
static const dt_pad_t kOptOut[] = {};
#else
#error Unsupported top
#endif

static uint8_t kPads[kDtPadCount] = {0};

// PLIC structures
static dif_pwrmgr_t pwrmgr;
static dif_pinmux_t pinmux;
static dif_rv_plic_t plic;

/**
 * External interrupt handler.
 */
bool ottf_handle_irq(uint32_t *exc_info, dt_instance_id_t devid,
                     dif_rv_plic_irq_id_t irq_id) {
  if (devid != dt_pwrmgr_instance_id(kDtPwrmgrAon)) {
    return false;
  }

  dt_pwrmgr_irq_t irq = dt_pwrmgr_irq_from_plic_id(kDtPwrmgrAon, irq_id);
  CHECK(irq == kDtPwrmgrIrqWakeup, "IRQ ID: %d is incorrect", irq);
  CHECK_DIF_OK(dif_pwrmgr_irq_acknowledge(&pwrmgr, irq));
  return true;
}

/** Configure pinmux retention value.
 *
 * Each gen32 can cover 16 PADs randomization. When each pad ret val draws
 * **3**, the code calls gen32_range to choose from 0 to 2.
 */
void draw_pinmux_ret(uint32_t num_pins, uint8_t *arr, const dt_pad_t *optout,
                     size_t num_optout) {
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

  for (dt_pad_t pad = 0; pad < kDtPadCount; ++pad) {
    dif_pinmux_index_t index;
    dif_pinmux_pad_kind_t type;
    CHECK_DIF_OK(dif_pinmux_pad_from_dt_pad(pad, &index, &type));
    if (type == kDifPinmuxPadKindDio) {
      LOG_INFO("DIO [%d]: %x", index, kPads[pad]);
    } else {
      LOG_INFO("MIO [%d]: %x", index, kPads[pad]);
    }
  }

  LOG_INFO("END Chosen Retention Types");
}

/**
 * Configure PADs retention types.
 *
 * @param pinmux Pinmux handle.
 */
void configure_pad_retention_types(dif_pinmux_t *pinmux) {
  LOG_INFO("Configuring PADs retention types in PINMUX...");

  for (dt_pad_t pad = 0; pad < kDtPadCount; pad++) {
    dif_pinmux_index_t index;
    dif_pinmux_pad_kind_t type;
    CHECK_DIF_OK(dif_pinmux_pad_from_dt_pad(pad, &index, &type));
    CHECK_DIF_OK(dif_pinmux_pad_sleep_enable(pinmux, index, type, kPads[pad]));
  }

  LOG_INFO("PADs retention modes are configured.");
}

bool lowpower_prep(dif_pwrmgr_t *pwrmgr, dif_pinmux_t *pinmux, bool deepsleep) {
  bool result = false;
  dif_pwrmgr_domain_config_t pwrmgr_domain_cfg = 0;

  LOG_INFO("Selecting PADs retention modes...");

  draw_pinmux_ret(kDtPadCount, kPads, kOptOut, ARRAYSIZE(kOptOut));

  print_chosen_values();

  // Configure pwrmgr to deep powerdown.
  configure_pad_retention_types(pinmux);

  CHECK_DIF_OK(dif_pwrmgr_get_domain_config(pwrmgr, &pwrmgr_domain_cfg));
  if (deepsleep) {
    pwrmgr_domain_cfg &= ~kDifPwrmgrDomainOptionMainPowerInLowPower;
  } else {
    pwrmgr_domain_cfg |= kDifPwrmgrDomainOptionMainPowerInLowPower;
  }
  CHECK_DIF_OK(dif_pwrmgr_set_domain_config(pwrmgr, pwrmgr_domain_cfg,
                                            kDifToggleDisabled));
  CHECK_DIF_OK(dif_pwrmgr_low_power_set_enabled(pwrmgr, kDifToggleEnabled,
                                                kDifToggleEnabled));

  LOG_INFO("Going to sleep");
  wait_for_interrupt();  // Entering deep power down.

  return result;
}

bool test_main(void) {
  bool result = false;

  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  CHECK_DIF_OK(dif_pwrmgr_init_from_dt(kDtPwrmgrAon, &pwrmgr));
  CHECK_DIF_OK(dif_pinmux_init_from_dt(kDtPinmuxAon, &pinmux));
  CHECK_DIF_OK(dif_rv_plic_init_from_dt(kDtRvPlic, &plic));

  if (UNWRAP(pwrmgr_testutils_is_wakeup_reason(&pwrmgr, 0)) == true) {
    uint32_t deep_powerdown_en = rand_testutils_gen32_range(0, 1);
    bool deepsleep = (deep_powerdown_en) ? true : false;

#if defined(OPENTITAN_IS_EARLGREY)
    // TODO(lowrisc/opentitan#15889): The weak pull on IOC3 needs to be
    // disabled for this test. Remove this later.
    dif_pinmux_pad_attr_t out_attr;
    dif_pinmux_pad_attr_t in_attr = {0};
    CHECK_DIF_OK(
        dif_pinmux_pad_write_attrs_dt(&pinmux, kDtPadIoc3, in_attr, &out_attr));
#elif defined(OPENTITAN_IS_DARJEELING)
    // Nothing to be done
#else
#error Unsupported top
#endif

    if (!deepsleep) {
      // Enable all the AON interrupts used in this test.
      static const uint32_t kPlicTarget = 0;
      rv_plic_testutils_irq_range_enable(
          &plic, kPlicTarget,
          dt_pwrmgr_irq_to_plic_id(kDtPwrmgrAon, kDtPwrmgrIrqWakeup),
          dt_pwrmgr_irq_to_plic_id(kDtPwrmgrAon, kDtPwrmgrIrqWakeup));
      // Enable pwrmgr interrupt
      CHECK_DIF_OK(dif_pwrmgr_irq_set_enabled(&pwrmgr, 0, kDifToggleEnabled));
    }

    result = lowpower_prep(&pwrmgr, &pinmux, deepsleep);
  }

  dif_pwrmgr_request_sources_t wakeup_sources;
  CHECK_DIF_OK(dif_pwrmgr_find_request_source(
      &pwrmgr, kDifPwrmgrReqTypeWakeup, dt_pinmux_instance_id(kDtPinmuxAon),
      kDtPinmuxWakeupPinWkupReq, &wakeup_sources));
  if (UNWRAP(pwrmgr_testutils_is_wakeup_reason(&pwrmgr, wakeup_sources))) {
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
