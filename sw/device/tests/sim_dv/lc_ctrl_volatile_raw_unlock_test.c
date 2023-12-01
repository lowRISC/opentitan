// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <stdbool.h>

#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/ip/lc_ctrl/dif/dif_lc_ctrl.h"
#include "sw/ip/lc_ctrl/test/utils/lc_ctrl_testutils.h"
#include "sw/lib/sw/device/base/bitfield.h"
#include "sw/lib/sw/device/base/memory.h"
#include "sw/lib/sw/device/base/mmio.h"
#include "sw/lib/sw/device/runtime/log.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"

static dif_lc_ctrl_t lc_ctrl;

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  CHECK_DIF_OK(dif_lc_ctrl_init(
      mmio_region_from_addr(TOP_DARJEELING_LC_CTRL_REGS_BASE_ADDR), &lc_ctrl));

  dif_lc_ctrl_state_t state;
  CHECK_DIF_OK(dif_lc_ctrl_get_state(&lc_ctrl, &state));
  CHECK(state == kDifLcCtrlStateTestUnlocked0);
  return true;
}
