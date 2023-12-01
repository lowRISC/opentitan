// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_IP_KEYMGR_DPE_TEST_UTILS_KEYMGR_DPE_TESTUTILS_H_
#define OPENTITAN_SW_IP_KEYMGR_DPE_TEST_UTILS_KEYMGR_DPE_TESTUTILS_H_

#include "sw/ip/keymgr_dpe/dif/dif_keymgr_dpe.h"
#include "sw/lib/sw/device/base/status.h"

/**
 * Locks OTP, restarts and initializes keymgr_dpe with UDS (a.k.a. the OTP
 * root key).
 *
 * This procedure essentially gets the keymgr_dpe into the stage where it
 * can be used for tests. An example is given below:
 * ```
 * void test_main(void) {
 *   // The following sets up keymgr_dpe and asks it to latch UDS.
 *   dif_keymgr_dpe_t keymgr_dpe;
 *   keymgr_dpe_testutils_startup(&keymgr_dpe);
 *
 *   // Remainder of test; optionally advance to CreatorRootKey state, generate
 *   // keys and identities.
 *   ...
 * }
 * ```
 *
 * @param[out] keymgr_dpe A key manager handle, may be uninitialized.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t keymgr_dpe_testutils_startup(dif_keymgr_dpe_t *keymgr_dpe);

/**
 * Issues a keymgr_dpe advance operation and wait for it to complete.
 *
 * @param keymgr_dpe A key manager handle.
 * @param params Inputs that are consumed by HW during advance operation.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t keymgr_dpe_testutils_advance_state(
    const dif_keymgr_dpe_t *keymgr_dpe,
    const dif_keymgr_dpe_advance_params_t *params);

/**
 * Issues a keymgr_dpe key generation operation and wait for it to complete.
 *
 * @param keymgr_dpe A key manager handle.
 * @param params Inputs that are consumed by HW during generate operation.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t keymgr_dpe_testutils_generate(
    const dif_keymgr_dpe_t *keymgr_dpe,
    const dif_keymgr_dpe_generate_params_t *params,
    dif_keymgr_dpe_output_t *key);

/**
 * Erase a keymgr_dpe slot.
 *
 * @param keymgr_dpe A key manager handle.
 * @param params A wrapper struct that contains the destination slot to be
 * erased.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t keymgr_dpe_testutils_erase_slot(
    const dif_keymgr_dpe_t *keymgr_dpe,
    const dif_keymgr_dpe_erase_params_t *params);

/**
 * Checks if the current keymgr_dpe state matches the expected state
 *
 * @param keymgr_dpe A key manager handle.
 * @param exp_state The expected key manager state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t keymgr_dpe_testutils_check_state(
    const dif_keymgr_dpe_t *keymgr_dpe, const dif_keymgr_dpe_state_t exp_state);

/**
 * Polling keymgr_dpe status until it becomes idle.
 * Fail the test if the status code indicates any error.
 *
 * @param keymgr_dpe A key manager handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t keymgr_dpe_testutils_wait_for_operation_done(
    const dif_keymgr_dpe_t *keymgr_dpe);

#endif  // OPENTITAN_SW_IP_KEYMGR_DPE_TEST_UTILS_KEYMGR_DPE_TESTUTILS_H_
