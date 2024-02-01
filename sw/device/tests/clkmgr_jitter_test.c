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

bool test_main(void) {
  dif_clkmgr_t clkmgr;
  CHECK_DIF_OK(dif_clkmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR), &clkmgr));
  // Get the initial jitter state. It might be enabled or disabled depending
  // on reset behavior - either is fine for the purposes of this test.
  dif_toggle_t state;
  CHECK_DIF_OK(dif_clkmgr_jitter_get_enabled(&clkmgr, &state));

  // Toggle the enable twice so that it ends up in its original state.
  for (int j = 0; j < 2; ++j) {
    dif_toggle_t expected_state =
        state == kDifToggleEnabled ? kDifToggleDisabled : kDifToggleEnabled;
    dif_toggle_t actual_state = state;
    CHECK_DIF_OK(dif_clkmgr_jitter_set_enabled(&clkmgr, expected_state));
    CHECK_DIF_OK(dif_clkmgr_jitter_get_enabled(&clkmgr, &actual_state));
    CHECK(actual_state == expected_state);
  }
  return true;
}
