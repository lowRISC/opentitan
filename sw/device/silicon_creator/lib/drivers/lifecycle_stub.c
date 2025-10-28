// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"

/*
 * English Breakfast does not have an lc_ctrl IP but this
 * function is still used for some non-lc_ctrl related tasks
 * in test_rom. Provide a stub just to make it work.
 */
void lifecycle_hw_rev_get(lifecycle_hw_rev_t *hw_rev) {
  *hw_rev = (lifecycle_hw_rev_t){
      .silicon_creator_id = 0,
      .product_id = 0,
      .revision_id = 0,
  };
}
