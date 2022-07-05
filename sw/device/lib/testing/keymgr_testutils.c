// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/keymgr_testutils.h"

#include "sw/device/lib/dif/dif_keymgr.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"

void keymgr_testutils_advance_state(const dif_keymgr_t *keymgr,
                                    const dif_keymgr_state_params_t *params) {
  CHECK_DIF_OK(dif_keymgr_advance_state(keymgr, params));
  keymgr_testutils_wait_for_operation_done(keymgr);
}

void keymgr_testutils_check_state(const dif_keymgr_t *keymgr,
                                  const dif_keymgr_state_t exp_state) {
  dif_keymgr_state_t act_state;
  CHECK_DIF_OK(dif_keymgr_get_state(keymgr, &act_state));
  CHECK(act_state == exp_state,
        "Keymgr in unexpected state: %x, expected to be %x", act_state,
        exp_state);
}

void keymgr_testutils_generate_identity(const dif_keymgr_t *keymgr) {
  CHECK_DIF_OK(dif_keymgr_generate_identity_seed(keymgr));
  keymgr_testutils_wait_for_operation_done(keymgr);
}

void keymgr_testutils_generate_versioned_key(
    const dif_keymgr_t *keymgr,
    const dif_keymgr_versioned_key_params_t params) {
  CHECK_DIF_OK(dif_keymgr_generate_versioned_key(keymgr, params));
  keymgr_testutils_wait_for_operation_done(keymgr);
}

void keymgr_testutils_disable(const dif_keymgr_t *keymgr) {
  CHECK_DIF_OK(dif_keymgr_disable(keymgr));
  keymgr_testutils_wait_for_operation_done(keymgr);
}

void keymgr_testutils_wait_for_operation_done(const dif_keymgr_t *keymgr) {
  dif_keymgr_status_codes_t status;
  do {
    CHECK_DIF_OK(dif_keymgr_get_status_codes(keymgr, &status));
  } while (status == 0);
  if (status != kDifKeymgrStatusCodeIdle) {
    LOG_ERROR("Unexpected status: %x", status);
  }
}
