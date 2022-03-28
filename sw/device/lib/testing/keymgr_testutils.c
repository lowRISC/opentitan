// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/keymgr_testutils.h"

#include "sw/device/lib/dif/dif_keymgr.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"

void keymgr_testutils_advance_state(const dif_keymgr_t *keymgr,
                                    const dif_keymgr_state_params_t *params) {
  CHECK_DIF_OK(dif_keymgr_advance_state(keymgr, params));

  while (true) {
    dif_keymgr_status_codes_t status;

    CHECK_DIF_OK(dif_keymgr_get_status_codes(keymgr, &status));
    if (status == 0) {
      LOG_INFO("Advancing to next state");
    } else if (status == kDifKeymgrStatusCodeIdle) {
      break;
    } else {
      LOG_ERROR("Unexpected status: %0x", status);
      break;
    }
  }
}

void keymgr_testutils_check_state(const dif_keymgr_t *keymgr,
                                  const dif_keymgr_state_t exp_state) {
  dif_keymgr_state_t act_state;
  CHECK_DIF_OK(dif_keymgr_get_state(keymgr, &act_state));
  if (act_state != exp_state) {
    LOG_INFO("Keymgr in unexpected state: %0x, expected to be %0x", act_state,
             exp_state);
  }
}
