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

  // Get the initial jitter state: this is right after reset so it should be
  // disabled.
  dif_toggle_t state;
  CHECK_DIF_OK(dif_clkmgr_jitter_get_enabled(&clkmgr, &state));
  CHECK(state == kDifToggleDisabled);
  // Check that enabling jitter doesn't depend on jitter_regwen.
  // Lock jitter_enable with jitter_regwen.
  CHECK_DIF_OK(dif_clkmgr_lock_jitter_enable(&clkmgr));
  // A write to enable succeeds.
  dif_toggle_t actual_state = kDifToggleDisabled;
  CHECK_DIF_OK(dif_clkmgr_jitter_set_enabled(&clkmgr));
  CHECK_DIF_OK(dif_clkmgr_jitter_get_enabled(&clkmgr, &actual_state));
  CHECK(actual_state == kDifToggleEnabled);
  return true;
}
