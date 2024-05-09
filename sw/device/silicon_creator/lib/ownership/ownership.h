// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_OWNERSHIP_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_OWNERSHIP_H_

#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/ownership/datatypes.h"
#include "sw/device/silicon_creator/lib/ownership/owner_block.h"

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
 * Initialize the owner pages from flash
 */
rom_error_t ownership_init(boot_data_t *bootdata, owner_config_t *config,
                           owner_application_keyring_t *keyring);

/**
 * Check if owner page 1 is valid for ownership transfer.
 *
 * @param bootdata The current bootdata.
 * @return kHardenedBoolTrue if page 1 is valid.
 */
hardened_bool_t ownership_page1_valid_for_transfer(boot_data_t *bootdata);

/**
 * Lockdown the flash configuration.
 *
 *
 * @param bootdata The current bootdata.
 * @param config The current owner configuration.
 * @return error state.
 */
rom_error_t ownership_flash_lockdown(boot_data_t *bootdata,
                                     const owner_config_t *config);

/**
 * Seal an owner page.
 *
 * Calculates and applies the seal to an owner page in RAM.
 *
 * @param page Which owner page to seal.
 */
void ownership_page_seal(size_t page);
#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_OWNERSHIP_H_
