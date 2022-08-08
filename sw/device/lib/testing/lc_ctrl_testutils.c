// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/lc_ctrl_testutils.h"

#include <stdbool.h>

#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"

bool lc_ctrl_testutils_debug_func_enabled(const dif_lc_ctrl_t *lc_ctrl) {
  dif_lc_ctrl_state_t state;
  CHECK_DIF_OK(dif_lc_ctrl_get_state(lc_ctrl, &state));

  switch (state) {
    case kDifLcCtrlStateTestUnlocked0:
    case kDifLcCtrlStateTestUnlocked1:
    case kDifLcCtrlStateTestUnlocked2:
    case kDifLcCtrlStateTestUnlocked3:
    case kDifLcCtrlStateTestUnlocked4:
    case kDifLcCtrlStateTestUnlocked5:
    case kDifLcCtrlStateTestUnlocked6:
    case kDifLcCtrlStateTestUnlocked7:
    case kDifLcCtrlStateDev:
    case kDifLcCtrlStateRma:
      return true;
    default:
      return false;
  }
}

void lc_ctrl_testutils_check_transition_count(const dif_lc_ctrl_t *lc_ctrl,
                                              uint8_t exp_lc_count) {
  LOG_INFO("Read LC count and check with expect_val=%0d", exp_lc_count);
  uint8_t lc_count;
  CHECK_DIF_OK(dif_lc_ctrl_get_attempts(lc_ctrl, &lc_count));
  CHECK(lc_count == exp_lc_count,
        "LC_count error, expected %0d but actual count is %0d", exp_lc_count,
        lc_count);
}

void lc_ctrl_testutils_check_lc_state(const dif_lc_ctrl_t *lc_ctrl,
                                      dif_lc_ctrl_state_t exp_lc_state) {
  LOG_INFO("Read LC state and check with expect_state=%0d", exp_lc_state);
  dif_lc_ctrl_state_t lc_state;
  CHECK_DIF_OK(dif_lc_ctrl_get_state(lc_ctrl, &lc_state));
  CHECK(lc_state == exp_lc_state,
        "LC_state error, expected %0d but actual state is %0d", exp_lc_state,
        lc_state);
}
