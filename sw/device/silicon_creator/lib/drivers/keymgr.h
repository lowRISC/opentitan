// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_KEYMGR_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_KEYMGR_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif

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
 * Advances the state of the key manager to Creator Root Key state.
 *
 * This operation is non-blocking to allow the software to continue with other
 * operations while the key manager is advancing its state. The caller is
 * responsible for calling the `keymgr_state_creator_check()` at a later time
 * to ensure the advance transition completed without errors.
 *
 * @param binding_value Software binding value extracted from the ROM_EXT
 * manifest.
 * @param max_key_version Maximum key version extracted from the ROM_EXT
 * manifest.
 * @return The result of the operation.
 */
// TODO: Switch binding_value to a wrapped struct parameter.
rom_error_t keymgr_state_advance_to_creator(const uint32_t binding_value[8],
                                            uint32_t max_key_version);

/**
 * Checks the state of the key manager.
 *
 * @return `kErrorOk` if the key manager is in Creator Root Key state and the
 * status is idle of success; otherwise retuns `kErrorKeymgrInternal`.
 */
rom_error_t keymgr_state_creator_check(void);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_KEYMGR_H_
