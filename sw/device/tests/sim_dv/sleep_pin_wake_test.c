// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

// PLIC structures
static const uint32_t kPlicTarget = kTopEarlgreyPlicTargetIbex0;
static dif_rv_plic_t plic;

// Volatile for vseq to assign random constant to select one of 8 MIO DIO
static volatile const uint8_t kWakeupSel = 0;

/**
 * Pins to be configured.
 *
 * Assign GPIO Pads to Pinmux so that sv sequence can drive GPIO PADs.
 */
static const uint32_t kGpioMask = 0x000001ff;

bool test_main(void) {
  dif_pwrmgr_t pwrmgr;
  dif_pinmux_t pinmux;
  dif_gpio_t gpio;

  dif_pinmux_index_t detector;
  dif_pinmux_wakeup_config_t wakeup_cfg;

  // Initialize power manager
  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));
  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &plic));
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));

  if (pwrmgr_testutils_is_wakeup_reason(&pwrmgr, 0)) {
    LOG_INFO("POR reset");

    // TODO: Enable Pwrmgr wake up event, PLIC, then configure PINMUX randomly
    // Assign GPIOs in the pinmux
    for (size_t i = 0; i < 32; ++i) {
      if (kGpioMask & (1u << i)) {
        dif_pinmux_index_t mio = kTopEarlgreyPinmuxMioOutIoa0 + i;
        dif_pinmux_index_t gpio_out = kTopEarlgreyPinmuxOutselGpioGpio0 + i;
        CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, mio, gpio_out));
        mio = kTopEarlgreyPinmuxInselIoa0 + i;
        dif_pinmux_index_t gpio_in =
            kTopEarlgreyPinmuxPeripheralInGpioGpio0 + i;
        CHECK_DIF_OK(dif_pinmux_input_select(&pinmux, gpio_in, mio));
      }
    }
    CHECK_DIF_OK(dif_gpio_init(
        mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR), &gpio));

    wakeup_cfg.mode = kDifPinmuxWakeupModePositiveEdge;
    wakeup_cfg.signal_filter = false;

    // TODO: Get the padkind from vseq
    wakeup_cfg.pad_type = kDifPinmuxPadKindMio;

    // TODO: Get the pad randomly from vseq
    // kTopEarlgreyPinmuxInselIoa0:kTopEarlgreyPinmuxInselLast if KinMio
    // 0: NUM_DIO_PADS-1 if KindDio
    wakeup_cfg.pad_select = kTopEarlgreyPinmuxInselIoa0;

    CHECK_DIF_OK(dif_pinmux_wakeup_detector_enable(
        &pinmux, (uint32_t)kWakeupSel, wakeup_cfg));

    // ...
    LOG_INFO("pinmux_init end");

    // Enter low power
    pwrmgr_testutils_enable_low_power(&pwrmgr,
                                      kDifPwrmgrWakeupRequestSourceThree, 0);

    LOG_INFO("Entering low power mode.");
    wait_for_interrupt();

    // TODO: Check WAKEUP_INFO and pin wake

  } else if (pwrmgr_testutils_is_wakeup_reason(
                 &pwrmgr, kDifPwrmgrWakeupRequestSourceThree)) {
    // Pinmux wakeup
    LOG_INFO("PINMUX PIN Wakeup");

    // TODO: Check if selected wakeup detector was triggerred.

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
