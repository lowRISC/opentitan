// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

/**
 * Test that all 'gateable' clocks, directly controlled by software,
 * can be enabled and disabled.
 */
static void test_gateable_clocks(const dif_clkmgr_t *clkmgr) {
  for (dif_clkmgr_gateable_clock_t clock = 0;
       clock <= kTopEarlgreyGateableClocksLast; ++clock) {
    // Get the initial state of the clock. The clock might be enabled or
    // disabled depending on reset behavior - either is fine for the purposes of
    // this test.
    dif_toggle_t state;
    CHECK_DIF_OK(dif_clkmgr_gateable_clock_get_enabled(clkmgr, clock, &state));

    // Toggle the enable twice so that it ends up in its original state.
    for (int j = 0; j < 2; ++j) {
      dif_toggle_t expected_state =
          state == kDifToggleEnabled ? kDifToggleDisabled : kDifToggleEnabled;
      dif_toggle_t actual_state = state;
      CHECK_DIF_OK(
          dif_clkmgr_gateable_clock_set_enabled(clkmgr, clock, expected_state));
      CHECK_DIF_OK(
          dif_clkmgr_gateable_clock_get_enabled(clkmgr, clock, &actual_state));
      CHECK(actual_state == expected_state);

      state = actual_state;
    }
  }
}

/**
 * Test that all 'hintable' clocks, indirectly controlled by software,
 * can have their hint toggled and status checked.
 */
void test_hintable_clocks(const dif_clkmgr_t *clkmgr) {
  for (dif_clkmgr_hintable_clock_t clock = 0;
       clock <= kTopEarlgreyHintableClocksLast; ++clock) {
    // Get the initial state of the hint for the clock The clock hint might be
    // enabled or disabled depending on reset behavior - either is fine for the
    // purposes of this test.
    dif_toggle_t state;
    CHECK_DIF_OK(dif_clkmgr_hintable_clock_get_hint(clkmgr, clock, &state));

    // Toggle the hint twice so that it ends up in its original state.
    for (int j = 0; j < 2; ++j) {
      dif_toggle_t expected_state =
          state == kDifToggleEnabled ? kDifToggleDisabled : kDifToggleEnabled;
      dif_toggle_t actual_state = state;
      CHECK_DIF_OK(
          dif_clkmgr_hintable_clock_set_hint(clkmgr, clock, expected_state));
      CHECK_DIF_OK(
          dif_clkmgr_hintable_clock_get_hint(clkmgr, clock, &actual_state));
      CHECK(actual_state == expected_state);

      // If the clock hint is enabled then the clock should always be enabled.
      if (actual_state == kDifToggleEnabled) {
        dif_toggle_t state = kDifToggleDisabled;
        CHECK_DIF_OK(
            dif_clkmgr_hintable_clock_get_enabled(clkmgr, clock, &state));
        CHECK(state == kDifToggleEnabled,
              "clock %u hint is enabled but status is disabled", clock);
      }

      state = actual_state;
    }
  }
}

bool test_main(void) {
  dif_clkmgr_t clkmgr;
  CHECK_DIF_OK(dif_clkmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR), &clkmgr));
  test_gateable_clocks(&clkmgr);
  test_hintable_clocks(&clkmgr);

  return true;
}
