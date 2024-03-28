// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_OWNER_BLOCK_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_OWNER_BLOCK_H_

#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/ownership/datatypes.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * The owner config struct contains high-level configuration items
 * from an owner block.
 */
typedef struct owner_config {
  /** The requested SRAM execution configuration. */
  owner_sram_exec_mode_t sram_exec;
  /** The requested flash configuration. */
  const owner_flash_config_t *flash;
  /** The requested flash INFO configuration. */
  const owner_flash_info_config_t *info;
  /** The requested rescue configuration. */
  const owner_rescue_config_t *rescue;
} owner_config_t;

/**
 * The application keyring collects application keys from the owner config
 * block.
 */
typedef struct owner_application_keyring {
  /** The number of application keys found. */
  size_t length;
  /** Pointers to the application keys. */
  const owner_application_key_t *key[16];
} owner_application_keyring_t;

/**
 * Initialize the owner config with default values.
 *
 * The sram_exec mode is set to DisabledLocked and the three configuration
 * pointers are set to kHardenedBoolFalse.
 *
 * @param config A pointer to a config struct holding pointers to config items.
 */
void owner_config_default(owner_config_t *config);

/**
 * Parse an owner block, extracting pointers to keys and configuration items.
 *
 * @param block The owner block to parse.
 * @param config A pointer to a config struct holding pointers to config items.
 * @param keyring A pointer to a keyring struct holding application key
 * pointers.
 * @return error code.
 */
rom_error_t owner_block_parse(const owner_block_t *block,
                              owner_config_t *config,
                              owner_application_keyring_t *keyring);

/**
 * Apply the flash configuration parameters from the owner block.
 *
 * @param flash A pointer to a flash configuration struct.
 * @param config_side Which side of the flash to configure.
 * @param primary_side Which side of the flash is primary.
 * @return error code.
 */
rom_error_t owner_block_flash_apply(const owner_flash_config_t *flash,
                                    uint32_t config_side,
                                    uint32_t primary_side);

/**
 * Apply the flash info configuration parameters from the owner block.
 *
 * @param info A pointer to a flash_info configuration.
 * @return error code.
 */
rom_error_t owner_block_info_apply(const owner_flash_info_config_t *info);

rom_error_t owner_keyring_find_key(const owner_application_keyring_t *keyring,
                                   uint32_t key_alg, uint32_t key_id,
                                   size_t *index);

/**
 * Determine whether a particular rescue command is allowed.
 *
 * @param rescue A pointer to the rescue configuration.
 * @param command The rescue command to check.
 * @return kHardenedBoolTrue if allowed.
 */
hardened_bool_t owner_rescue_command_allowed(
    const owner_rescue_config_t *rescue, uint32_t command);
#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus
#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_OWNER_BLOCK_H_
