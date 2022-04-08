// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_KEYMGR_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_KEYMGR_TESTUTILS_H_

#include "sw/device/lib/dif/dif_keymgr.h"

/**
 * Issues a keymgr advance operation and wait for it to complete
 *
 * @param keymgr A key manager handle.
 * @param params The binding and max key version value for the next state.
 */
void keymgr_testutils_advance_state(const dif_keymgr_t *keymgr,
                                    const dif_keymgr_state_params_t *params);

/**
 * Checks if the current keymgr state matches the expected state
 *
 * @param keymgr A key manager handle.
 * @param exp_state The expected key manager state.
 */
void keymgr_testutils_check_state(const dif_keymgr_t *keymgr,
                                  const dif_keymgr_state_t exp_state);

/**
 * Issues a keymgr identity generation and wait for it to complete
 *
 * @param keymgr A key manager handle.
 */
void keymgr_testutils_generate_identity(const dif_keymgr_t *keymgr);

/**
 * Issues a keymgr HW/SW versioned key generation and wait for it to complete
 *
 * @param keymgr A key manager handle.
 * @param params Key generation parameters.
 */
void keymgr_testutils_generate_versioned_key(
    const dif_keymgr_t *keymgr, const dif_keymgr_versioned_key_params_t params);

/**
 * Issues a keymgr disable and wait for it to complete
 */
void keymgr_testutils_disable(const dif_keymgr_t *keymgr);

/**
 * Polling keymgr status until it becomes idle.
 * Fail the test if the status code indicates any error.
 *
 * @param keymgr A key manager handle.
 */
void keymgr_testutils_wait_for_operation_done(const dif_keymgr_t *keymgr);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_KEYMGR_TESTUTILS_H_
