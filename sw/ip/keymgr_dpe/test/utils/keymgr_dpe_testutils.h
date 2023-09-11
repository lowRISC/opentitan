// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_IP_KEYMGR_DPE_TEST_UTILS_KEYMGR_DPE_TESTUTILS_H_
#define OPENTITAN_SW_IP_KEYMGR_DPE_TEST_UTILS_KEYMGR_DPE_TESTUTILS_H_

#include "sw/ip/flash_ctrl/dif/dif_flash_ctrl.h"
#include "sw/ip/keymgr_dpe/dif/dif_keymgr_dpe.h"
#include "sw/lib/sw/device/base/status.h"

/**
 * Struct to hold the creator or owner secrets for the key manager. In the spec,
 * these are also known as `creator_div_secret` and `owner_div_secret`
 * respectively. Both these values are stored in the flash memory, therefore
 * these structs are useful to set and write these two secrets with
 * `keymgr_dpe_testutils_flash_init` function provided below.
 */
typedef struct keymgr_dpe_testutils_secret {
  uint32_t value[8];
} keymgr_dpe_testutils_secret_t;

/**
 * Key manager Creator Secret (a.k.a. `creator_div_secret`) stored in info flash
 * page.
 */
static const keymgr_dpe_testutils_secret_t kCreatorSecret = {
    .value = {0x4e919d54, 0x322288d8, 0x4bd127c7, 0x9f89bc56, 0xb4fb0fdf,
              0x1ca1567b, 0x13a0e876, 0xa6521d8f}};

/**
 * Key manager Owner Secret (a.k.a. `owner_div_secret`) stored in info flash
 * page.
 */
static const keymgr_dpe_testutils_secret_t kOwnerSecret = {.value = {
                                                               0xa6521d8f,
                                                               0x13a0e876,
                                                               0x1ca1567b,
                                                               0xb4fb0fdf,
                                                               0x9f89bc56,
                                                               0x4bd127c7,
                                                               0x322288d8,
                                                               0x4e919d54,
                                                           }};

/**
 * Programs flash with secrets so that a keymgr_dpe slot can be advanced from
 * UDS stage to the next stage (a.k.a. CreatorRootKey in the old keymgr
 * terminology).
 *
 * This is normally a subfunction of `keymgr_dpe_testutils_startup`, but some
 * tests use the function separately as well.
 *
 * @param flash[out] An unitialized flash_ctrl handle.
 * @param creator_secret The creator secret to be programmed to flash.
 * @param owner_secret The owner secret to be programmed to flash.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t keymgr_dpe_testutils_flash_init(
    dif_flash_ctrl_state_t *flash,
    const keymgr_dpe_testutils_secret_t *creator_secret,
    const keymgr_dpe_testutils_secret_t *owner_secret);

/**
 * Programs flash, restarts and initializes keymgr_dpe with UDS (a.k.a. the OTP
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
