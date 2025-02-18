// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "clkmgr_regs.h"

OTTF_DEFINE_TEST_CONFIG();

void test_jitter_locked(const dif_clkmgr_t *clkmgr,
                        dif_toggle_t initial_state) {
  // Lock jitter enable.
  CHECK_DIF_OK(dif_clkmgr_lock_jitter_enable(clkmgr));
  // To make sure the write is performed the dif function must be bypassed
  // since it blocks the write if regwen is off.
  dif_toggle_t opposite_state = initial_state == kDifToggleEnabled
                                    ? kDifToggleDisabled
                                    : kDifToggleEnabled;
  multi_bit_bool_t opposite_mubi_state = opposite_state == kDifToggleEnabled
                                             ? kMultiBitBool4True
                                             : kMultiBitBool4False;
  mmio_region_write32(clkmgr->base_addr, CLKMGR_JITTER_ENABLE_REG_OFFSET,
                      opposite_mubi_state);

  dif_toggle_t actual_state = opposite_state;
  CHECK_DIF_OK(dif_clkmgr_jitter_get_enabled(clkmgr, &actual_state));
  CHECK(actual_state == initial_state);
}

bool test_main(void) {
  dif_clkmgr_t clkmgr;
  CHECK_DIF_OK(dif_clkmgr_init_from_dt(kDtClkmgrAon, &clkmgr));

  // Get the initial jitter state. It might be enabled or disabled depending
  // on reset behavior - either is fine for the purposes of this test.
  dif_toggle_t state;
  CHECK_DIF_OK(dif_clkmgr_jitter_get_enabled(&clkmgr, &state));

  bool locked;
  CHECK_DIF_OK(dif_clkmgr_jitter_enable_is_locked(&clkmgr, &locked));

  // If it is unlocked check the state can be modified.
  if (!locked) {
    // Toggle the enable twice so that it ends up in its original state.
    for (int j = 0; j < 2; ++j) {
      dif_toggle_t expected_state =
          state == kDifToggleEnabled ? kDifToggleDisabled : kDifToggleEnabled;
      dif_toggle_t actual_state = state;
      CHECK_DIF_OK(dif_clkmgr_jitter_set_enabled(&clkmgr, expected_state));
      CHECK_DIF_OK(dif_clkmgr_jitter_get_enabled(&clkmgr, &actual_state));
      CHECK(actual_state == expected_state);
      state = actual_state;
    }
  }
  // Check jitter_regwen disabled, so jitter_enable is locked. Do it at the end
  // since jitter_regwen will remain locked until reset.
  test_jitter_locked(&clkmgr, state);
  return true;
}
