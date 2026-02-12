// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

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
#if defined(TEST_JITTER_DISABLED)
  CHECK(state == kDifToggleDisabled);
#elif defined(TEST_JITTER_ENABLED)
  CHECK(state == kDifToggleEnabled);
#else
#error "no jitter test variant is defined"
#endif
  return true;
}
