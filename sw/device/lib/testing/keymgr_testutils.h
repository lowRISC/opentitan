// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_KEYMGR_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_KEYMGR_TESTUTILS_H_

#include "sw/device/lib/dif/dif_keymgr.h"

/**
 * Issues a keymgr advance operation and wait for it to complete
 */
void keymgr_testutils_advance_state(const dif_keymgr_t *keymgr,
                                    const dif_keymgr_state_params_t *params);

/**
 * Checks if the current keymgr state matches the expected state
 */
void keymgr_testutils_check_state(const dif_keymgr_t *keymgr,
                                  const dif_keymgr_state_t exp_state);

/**
 * Issues a keymgr identity generation and wait for it to complete
 */
void keymgr_testutils_generate_identity(const dif_keymgr_t *keymgr);

/**
 * Issues a keymgr HW/SW versioned key generation and wait for it to complete
 */
void keymgr_testutils_generate_versioned_key(
    const dif_keymgr_t *keymgr, const dif_keymgr_versioned_key_params_t params);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_KEYMGR_TESTUTILS_H_
