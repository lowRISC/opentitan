// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_KEYMGR_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_KEYMGR_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/keymgr_binding_value.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Key Manager states.
 */
typedef enum keymgr_state {
  /**
   * Key manager control is still in reset. Please wait for initialization
   * complete before issuing operations
   */
  kKeymgrStateReset,
  /**
   * Key manager control has finished initialization and will now accept
   * software commands.
   */
  kKeymgrStateInit,
  /**
   * Key manager control currently contains the creator root key.
   */
  kKeymgrStateCreatorRootKey,
  /**
   * Key manager control currently contains the owner intermediate key.
   */
  kKeymgrStateOwnerIntermediateKey,
  /**
   * Key manager control currently contains the owner key.
   */
  kKeymgrStateOwnerKey,
  /**
   * Key manager currently disabled. Please reset the key manager. Sideload keys
   * are still valid.
   */
  kKeymgrStateDisabled,
  /**
   * Key manager currently invalid. Please reset the key manager. Sideload keys
   * are no longer valid.
   */
  kKeymgrStateInvalid,
  /**
   * This is not a state - it is the total number of states.
   */
  kKeymgrStateNumStates,
} keymgr_state_t;

/**
 * Sets the key manager inputs.
 *
 * @param binding_value Software binding value from the manifest of the next
 * stage.
 * @param max_key_version Maximum key version from the manifest of the next
 * stage.
 */
void keymgr_set_next_stage_inputs(
    const keymgr_binding_value_t *binding_value_sealing,
    const keymgr_binding_value_t *binding_value_attestation,
    uint32_t max_key_version);

/**
 * Initializes the key manager.
 *
 * Initializes the key manager `entropy_reseed_interval` and advances the state
 * into initialized.
 *
 * The working status of the key manager must be set to reset before
 * calling this function otherwise it will return `kErrorKeymgrInternal`.
 *
 * @param entropy_reseed_interval Number of key manager cycles before the
 * entropy is reseeded.
 * @return The result of the operation.
 */
rom_error_t keymgr_init(uint16_t entropy_reseed_interval);

/**
 * Advances the state of the key manager.
 *
 * The `keymgr_check_state()` function must be called before this function to
 * ensure the key manager is in the expected state and ready to receive op
 * commands.
 *
 * The caller is responsible for calling the `keymgr_check_state()` at a later
 * time to ensure the advance transition completed without errors.
 */
void keymgr_advance_state(void);

/**
 * Checks the state of the key manager.
 *
 * @param expected_state Expected key manager state.
 * @return `kErrorOk` if the key manager is in `expected_state` and the status
 * is idle or success; otherwise returns `kErrorKeymgrInternal`.
 */
rom_error_t keymgr_check_state(keymgr_state_t expected_state);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_KEYMGR_H_
