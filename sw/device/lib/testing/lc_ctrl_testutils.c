// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/lc_ctrl_testutils.h"

#include <stdbool.h>

#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/runtime/ibex.h"
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

/*
 * LC_CTRL operation status timeout in micro seconds.
 *
 * It is not possible to predict the specific cycle count that a LC_CTRL
 * finishes its operation, thus arbitrary value of 100us is used.
 */
const uint8_t kLcOpTimeoutUs = 100;

/**
 * Checks status is ready.
 */
static bool lc_ready(const dif_lc_ctrl_t *lc_ctrl) {
  dif_lc_ctrl_status_t status;
  CHECK_DIF_OK(dif_lc_ctrl_get_status(lc_ctrl, &status));
  return bitfield_bit32_read(status, kDifLcCtrlStatusCodeReady);
}

void lc_ctrl_testutils_wait_for_idle(const dif_lc_ctrl_t *lc_ctrl) {
  IBEX_SPIN_FOR(lc_ready(lc_ctrl), kLcOpTimeoutUs);
}
