// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_KEYMGR_DPE_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_KEYMGR_DPE_TESTUTILS_H_

// This #if define ... ensures backwards compatibility with darjeeling. Either
// both tops will get their own testutils or this define guard can be
// implemented at a more granular level (i.e. at function level).
#if defined(OPENTITAN_IS_DARJEELING)

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_keymgr_dpe.h"

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
status_t keymgr_dpe_testutils_startup(dif_keymgr_dpe_t *keymgr_dpe,
                                      uint32_t slot_dst_sel);

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

#elif defined(OPENTITAN_IS_EARLGREY) || defined(OPENTITAN_IS_ENGLISHBREAKFAST)

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_keymgr_dpe.h"
#include "sw/device/lib/dif/dif_kmac.h"

// Note: In the testutil only a single key derivation chain is generated,
// rather than two key chains (attestation and sealing keys)

/**
 * Versioned key parameters for testing.
 *
 * Change destination in order to sideload keys to hardware.
 */
static const dif_keymgr_dpe_generate_params_t kKeyVersionedParams = {
    .key_dest = kDifKeymgrDpeKeyDestNone,
    .sideload_key = false,
    .salt = {0xb6521d8f, 0x13a0e876, 0x1ca1567b, 0xb4fb0fdf, 0x9f89bc56,
             0x4bd127c7, 0x322288d8, 0xde919d54},
    .version = 0x11,
    .slot_src_sel = 1,
};

/**
 * Parameter list for the initial advancement. The slot_dst_sel determines in
 * which slot the UDS is loaded. Any other parameters are discarded.
 */
static const dif_keymgr_dpe_advance_params_t kInitialParams = {
    .binding_value = {0, 0, 0, 0, 0, 0, 0, 0},
    .max_key_version = 0,
    .slot_src_sel = 0,
    .slot_dst_sel = 1,
    .slot_policy = 0};

/**
 * Parameters for advancing: UDS > creator root key
 */
static const dif_keymgr_dpe_advance_params_t kCreatorRootKeyParams = {
    .binding_value = {0xdc96c23d, 0xaf36e268, 0xcb68ff71, 0xe92f76e2,
                      0xb8a8379d, 0x426dc745, 0x19f5cff7, 0x4ec9c6d6},
    .max_key_version = 0x11,
    .slot_src_sel = 1,
    .slot_dst_sel = 1,
    .slot_policy = 1  // 0b001 Allow children without retaining the parent
};

/**
 * Parameter for advancing: creator root key > owner int key
 */
static const dif_keymgr_dpe_advance_params_t kOwnerIntKeyParams = {
    .binding_value = {0xe4987b39, 0x3f83d390, 0xc2f3bbaf, 0x3195dbfa,
                      0x23fb480c, 0xb012ae5e, 0xf1394d28, 0x1940ceeb},
    .max_key_version = 0xaa,
    .slot_src_sel = 1,
    .slot_dst_sel = 1,
    .slot_policy = 1  // 0b001 Allow children without retaining the parent
};

/**
 * Parameter for advancing: owner int key > owner key
 */
static const dif_keymgr_dpe_advance_params_t kOwnerKeyParams = {
    .binding_value = {0xd8a812ea, 0xb6ebe129, 0x217773d4, 0x35b37c77,
                      0xec8298be, 0x1f7dec77, 0x1803199e, 0xa02ad81d},
    .max_key_version = 0xaa,
    .slot_src_sel = 1,
    .slot_dst_sel = 1,
    .slot_policy = 5  // 0b101 Allow children with retaining the parent
};

/**
 * Struct to hold the creator or owner secrets for the key manager dpe.
 */
typedef struct keymgr_dpe_testutils_secret {
  uint32_t value[8];
} keymgr_dpe_testutils_secret_t;

/**
 * Key manager dpe Creator Secret (seed) stored in info flash page.
 */
static const keymgr_dpe_testutils_secret_t kCreatorSecret = {
    .value = {0x4e919d54, 0x322288d8, 0x4bd127c7, 0x9f89bc56, 0xb4fb0fdf,
              0x1ca1567b, 0x13a0e876, 0xa6521d8f}};

/**
 * Key manager dpe Owner Secret (seed) stored in info flash page.
 */
static const keymgr_dpe_testutils_secret_t kOwnerSecret = {
    .value = {0xa6521d8f, 0x13a0e876, 0x1ca1567b, 0xb4fb0fdf, 0x9f89bc56,
              0x4bd127c7, 0x322288d8, 0x4e919d54}};

/**
 * Programs flash with secrets so that the keymgr dpe can be advanced to
 * CreatorRootKey state.
 *
 * This is normally a subfunction of keymgr_testutils_startup, but some tests
 * use the function separately as well.
 *
 * @param flash An initialized flash_ctrl handle.
 * @param creator_secret The creator secret to be programmed to flash.
 * @param owner_secret The owner secret to be programmed to flash.
 *
 */
OT_WARN_UNUSED_RESULT
status_t keymgr_dpe_testutils_flash_init(
    dif_flash_ctrl_state_t *flash,
    const keymgr_dpe_testutils_secret_t *creator_secret,
    const keymgr_dpe_testutils_secret_t *owner_secret);

/**
 * Initializes the key manager dpe and its dependencies for testing.
 *
 * This function initializes the key manager dpe and its dependencies for
 * testing.
 *
 * This function will call `keymgr_dpe_testutils_try_startup()` if the boot
 * stage is `kBootStageOwner`; otherwise, it will call
 * `keymgr_testutils_startup()`. Additional checks are performed to ensure that
 * the key manager is in a valid state, and ready to perform key derivations.
 *
 * @param keymgr_dpe A key manager dpe handle, may be uninitialized.
 * @param kmac A KMAC handle, may be uninitialized.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t keymgr_dpe_testutils_initialize(dif_keymgr_dpe_t *keymgr_dpe,
                                         dif_kmac_t *kmac);

/**
 * Wrapper function to `keymgr_testutils_startup()`.
 *
 * This function checks the state of the key manager before attempting to
 * initialize its dependencies and state.
 *
 * The function will return an error if the keymgr is disabled or in invalid
 * state.
 *
 * @param keymgr_dpe A key manager dpe handle, may be uninitialized.
 * @param kmac A KMAC handle, may be uninitialized.
 * @param keymgr_dpe_state pointer to store the current keymgr_dpe state
 * @param[out] keymgr_dpe_state The state of the keymgr after startup.
 */
OT_WARN_UNUSED_RESULT
status_t keymgr_dpe_testutils_try_startup(
    dif_keymgr_dpe_t *keymgr_dpe, dif_kmac_t *kmac,
    dif_keymgr_dpe_state_t *keymgr_dpe_state);

/**
 * Initialize non-volatile memory (flash and OTP) for keymgr dpe and then
 * reset, so that the relevant OTP partitions become accessible to keymgr dpe.
 * After calling this function, keymgr dpe can be initialized.
 */
OT_WARN_UNUSED_RESULT
status_t keymgr_dpe_testutils_init_nvm_then_reset(void);

/**
 * Programs flash, restarts, and advances keymgr to Available state.
 * Afterwards the CreatorRootKey is generated in the slot defined by
 * kCreatorRootKeyParams. Note that this function assumes that the keymgr dpe
 * is in the initial reset state after ROM execution.
 *
 * This procedure essentially gets the keymgr into the first state where it can
 * be used for tests. Tests should call it before anything else, like below:
 *
 * void test_main(void) {
 *   // Set up and generate the CreatorRootKey.
 *   dif_keymgr_dpe_t keymgr_dpe;
 *   dif_kmac_t kmac;
 *   keymgr_dpe_testutils_startup(&keymgr_dpe, &kmac);
 *
 *   // Remainder of test; optionally advance the CreatorRootKey to the
 *   // OwnerIntKey, generate keys and identities.
 *   ...
 * }
 *
 * Because the key manager dpe uses KMAC, this procedure also initializes and
 * configures KMAC. Software should not rely on the configuration here and
 * should reconfigure KMAC if needed. The purpose of configuring KMAC in this
 * procedure is so that the key manager dpe will not use KMAC with the default
 * entropy settings.
 *
 * @param keymgr_dpe A key manager dpe handle, may be uninitialized.
 * @param kmac A KMAC handle, may be uninitialized.
 */
OT_WARN_UNUSED_RESULT
status_t keymgr_dpe_testutils_startup(dif_keymgr_dpe_t *keymgr_dpe,
                                      dif_kmac_t *kmac);

/**
 * Advances the DPE context of the keymgr_dpe and wait for it to complete
 *
 * @param keymgr_dpe A key manager dpe handle.
 * @param params The binding and max key version value for the next state.
 */
OT_WARN_UNUSED_RESULT
status_t keymgr_dpe_testutils_advance_state(
    const dif_keymgr_dpe_t *keymgr_dpe,
    const dif_keymgr_dpe_advance_params_t *params);

/**
 * Loads the UDS into the keymgr dpe and move the state from `Reset`
 * to `Available`.
 *
 * The first advance call is automatically mapped to latch the UDS into the
 * designated destination slot rather than advancing any DPE context.
 * Therefore most registers used in the regular advance call are ignored
 * during initialization.
 *
 * @param keymgr_dpe A key manager dpe handle.
 * @param params The .slot_dst_sel subfield determines the slot for the UDS
 */
OT_WARN_UNUSED_RESULT
status_t keymgr_dpe_testutils_initial_load_uds(
    const dif_keymgr_dpe_t *keymgr_dpe,
    const dif_keymgr_dpe_advance_params_t *params);

/**
 * Checks if the current keymgr dpe state matches the expected state
 *
 * @param keymgr_dpe A key manager dpe handle.
 * @param exp_state The expected key manager state.
 */
OT_WARN_UNUSED_RESULT
status_t keymgr_dpe_testutils_check_state(
    const dif_keymgr_dpe_t *keymgr_dpe, const dif_keymgr_dpe_state_t exp_state);

/**
 * Issues a keymgr dpe HW/SW versioned key generation and wait for it
 * to complete.
 *
 * @param keymgr_dpe A key manager dpe handle.
 * @param params Key generation parameters.
 */
OT_WARN_UNUSED_RESULT
status_t keymgr_dpe_testutils_generate_key(
    const dif_keymgr_dpe_t *keymgr_dpe,
    const dif_keymgr_dpe_generate_params_t *params);

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
 * Issues a keymgr dpe disable and wait for it to complete
 */
OT_WARN_UNUSED_RESULT
status_t keymgr_dpe_testutils_disable(const dif_keymgr_dpe_t *keymgr_dpe);

/**
 * Polling keymgr dpe status until it becomes idle.
 * Fail the test if the status code indicates any error.
 *
 * @param keymgr_dpe A key manager dpe handle.
 */
OT_WARN_UNUSED_RESULT
status_t keymgr_dpe_testutils_wait_for_operation_done(
    const dif_keymgr_dpe_t *keymgr_dpe);

/**
 * Get the current state of the key manager dpe.
 *
 * @param keymgr_dpe A key manager dpe handle.
 * @param[out] state The current state of the key manager dpe in
 * C string format.
 *
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t keymgr_dpe_testutils_state_string_get(
    const dif_keymgr_dpe_t *keymgr_dpe, const char **stage_name);

/**
 * Clears the key from one sideload slot
 *
 * @param keymgr_dpe A key manager dpe handle.
 * @param clear_dest Destination for the clear operation
 *
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t keymgr_dpe_testutils_clear_sideload_key(
    const dif_keymgr_dpe_t *keymgr_dpe,
    dif_keymgr_dpe_sideload_clr_t clear_dest);

#else
#error "[Keymgr_dpe, testutils] None of the supported tops defined!"
#endif

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_KEYMGR_DPE_TESTUTILS_H_
