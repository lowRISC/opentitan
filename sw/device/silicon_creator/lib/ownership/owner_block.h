// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_OWNER_BLOCK_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_OWNER_BLOCK_H_

#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/ownership/datatypes.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * The signature or sealing status of an owner page.
 */
typedef enum owner_page_status {
  /** Invalid: `INV_`. */
  kOwnerPageStatusInvalid = 0x5f564e49,
  /** Sealed: `SEAL`. */
  kOwnerPageStatusSealed = 0x4c414553,
  /** Signed: `SIGN`. */
  kOwnerPageStatusSigned = 0x4e474953,
} owner_page_status_t;

/**
 * RAM copies of the owner pages read out of flash INFO pages.
 */
extern owner_block_t owner_page[2];
extern owner_page_status_t owner_page_valid[2];

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
 * Check if owner page 1 is valid for ownership transfer.
 *
 * @param bootdata The current bootdata.
 * @return kHardenedBoolTrue if page 1 is valid.
 */
hardened_bool_t owner_block_page1_valid_for_transfer(boot_data_t *bootdata);

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
 * @param lockdown Apply any special lockdown configuration to the specified
 *                 side of the flash.  May use kHardenedBoolFalse to skip
 *                 lockdown.
 * @return error code.
 */
rom_error_t owner_block_flash_apply(const owner_flash_config_t *flash,
                                    uint32_t config_side, uint32_t lockdown);

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
