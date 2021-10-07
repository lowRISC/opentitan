// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_framework/test_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

const test_config_t kTestConfig;

/**
 * Test that all 'gateable' clocks, directly controlled by software,
 * can be enabled and disabled.
 */
static void test_gateable_clocks(const dif_clkmgr_t *clkmgr,
                                 dif_clkmgr_params_t params) {
  const dif_clkmgr_gateable_clock_t clocks[] = {
      kTopEarlgreyGateableClocksIoDiv4Peri,
      kTopEarlgreyGateableClocksUsbPeri,
  };

  for (int i = 0; i < ARRAYSIZE(clocks); ++i) {
    dif_clkmgr_gateable_clock_t clock = clocks[i];

    // Get the initial state of the clock. The clock might be enabled or
    // disabled depending on reset behavior - either is fine for the purposes of
    // this test.
    bool enabled;
    CHECK_DIF_OK(
        dif_clkmgr_gateable_clock_get_enabled(clkmgr, params, clock, &enabled));

    // Toggle the enable twice so that it ends up in its original state.
    for (int j = 0; j < 2; ++j) {
      bool expected = !enabled;
      CHECK_DIF_OK(dif_clkmgr_gateable_clock_set_enabled(
          clkmgr, params, clock,
          expected ? kDifToggleEnabled : kDifToggleDisabled));
      CHECK_DIF_OK(dif_clkmgr_gateable_clock_get_enabled(clkmgr, params, clock,
                                                         &enabled));
      CHECK(enabled == expected);
    }
  }
}

/**
 * Test that all 'hintable' clocks, indirectly controlled by software,
 * can have their hint toggled and status checked.
 */
void test_hintable_clocks(const dif_clkmgr_t *clkmgr,
                          dif_clkmgr_params_t params) {
  const dif_clkmgr_hintable_clock_t clocks[] = {
      kTopEarlgreyHintableClocksMainAes,
      kTopEarlgreyHintableClocksMainHmac,
      kTopEarlgreyHintableClocksMainKmac,
      kTopEarlgreyHintableClocksMainOtbn,
  };

  for (int i = 0; i < ARRAYSIZE(clocks); ++i) {
    dif_clkmgr_hintable_clock_t clock = clocks[i];

    // Get the initial state of the hint for the clock The clock hint might be
    // enabled or disabled depending on reset behavior - either is fine for the
    // purposes of this test.
    bool enabled;
    CHECK_DIF_OK(
        dif_clkmgr_hintable_clock_get_hint(clkmgr, params, clock, &enabled));

    // Toggle the hint twice so that it ends up in its original state.
    for (int j = 0; j < 2; ++j) {
      bool expected = !enabled;
      CHECK_DIF_OK(dif_clkmgr_hintable_clock_set_hint(
          clkmgr, params, clock,
          expected ? kDifToggleEnabled : kDifToggleDisabled));
      CHECK_DIF_OK(
          dif_clkmgr_hintable_clock_get_hint(clkmgr, params, clock, &enabled));
      CHECK(enabled == expected);

      // If the clock hint is enabled then the clock should always be enabled.
      if (enabled) {
        bool status = false;
        CHECK_DIF_OK(dif_clkmgr_hintable_clock_get_enabled(clkmgr, params,
                                                           clock, &status));
        CHECK(status, "clock %u hint is enabled but status is disabled", clock);
      }
    }
  }
}

bool test_main() {
  const dif_clkmgr_params_t params = {
      .last_gateable_clock = kTopEarlgreyGateableClocksLast,
      .last_hintable_clock = kTopEarlgreyHintableClocksLast,
  };

  dif_clkmgr_t clkmgr;
  CHECK_DIF_OK(
      dif_clkmgr_init(mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR),
                      params, &clkmgr));
  test_gateable_clocks(&clkmgr, params);
  test_hintable_clocks(&clkmgr, params);

  return true;
}
