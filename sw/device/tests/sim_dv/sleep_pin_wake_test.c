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
#include "sw/device/lib/testing/rand_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

// PLIC structures
static const uint32_t kPlicTarget = kTopEarlgreyPlicTargetIbex0;
static dif_rv_plic_t plic;

// Volatile for vseq to assign random constant to select one of 8 MIO DIO
static volatile const uint8_t kWakeupSel = 0;

static const uint32_t kNumDio = 16;  // top_earlgrey has 16 DIOs

// kDirectDio is a list of Dio index that TB cannot control the PAD value.
// The list should be incremental order (see the code below)
#define NUM_DIRECT_DIO 5
static const uint32_t kDirectDio [NUM_DIRECT_DIO] = { 6, 12, 13, 14, 15};

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

    LOG_INFO("pinmux_init end");

    // Prepare which PAD SW want to select
    uint32_t mio0_dio1 = rand_testutils_gen32_range(0, 1);
    uint32_t pad_sel = 0;

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
    } else {
      // MIO: 0, 1 are tie-0, tie-1
      pad_sel = rand_testutils_gen32_range(2, kTopEarlgreyPinmuxInselLast);
    }

    // Send selection to SV vseq.
    LOG_INFO("Pad Selection: %d / %d", mio0_dio1, pad_sel);

    wakeup_cfg.mode = kDifPinmuxWakeupModePositiveEdge;
    wakeup_cfg.signal_filter = false;
    wakeup_cfg.pad_type = mio0_dio1;
    wakeup_cfg.pad_select = pad_sel;

    CHECK_DIF_OK(dif_pinmux_wakeup_detector_enable(
        &pinmux, (uint32_t)kWakeupSel, wakeup_cfg));

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
