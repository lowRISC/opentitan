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
 * Initialize the owner pages from flash
 */
rom_error_t ownership_init(boot_data_t *bootdata, owner_config_t *config,
                           owner_application_keyring_t *keyring);

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

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_OWNERSHIP_H_
