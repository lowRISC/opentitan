// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom_ext/sival/sival_owner.h"

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/dbg_print.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/ownership/owner_block.h"
#include "sw/device/silicon_creator/lib/ownership/ownership.h"
#include "sw/device/silicon_creator/lib/ownership/ownership_key.h"

/*
 * This module overrides the weak `sku_creator_owner_init` symbol in
 * ownership.c, thus allowing FPGA builds to install an owner configuration
 * simply by booting the ROM_EXT.
 */
rom_error_t sku_creator_owner_init(boot_data_t *bootdata) {
  const owner_keydata_t *owner =
      &((const owner_block_t *)sival_owner)->owner_key;
  uint32_t config_version =
      ((const owner_block_t *)sival_owner)->config_version;
  ownership_state_t state = bootdata->ownership_state;

  if (state == kOwnershipStateUnlockedSelf ||
      state == kOwnershipStateUnlockedAny ||
      state == kOwnershipStateUnlockedEndorsed) {
    // Nothing to do when in an unlocked state.
    return kErrorOk;
  } else if (state == kOwnershipStateLockedOwner) {
    if (hardened_memeq(owner->raw, owner_page[0].owner_key.raw,
                       ARRAYSIZE(owner->raw)) != kHardenedBoolTrue ||
        config_version <= owner_page[0].config_version) {
      // Different owner or already newest config version; nothing to do.
      return kErrorOk;
    }
  } else {
    // State is an unknown value, which is the same as kOwnershipStateRecovery.
    // We'll not return, thus allowing the owner config below to be programmed
    // into flash.
  }

  memset(&owner_page[0], 0x5a, sizeof(owner_page[0]));
  memcpy(&owner_page[0], sival_owner, sizeof(sival_owner));

  // Check that the owner_block will parse correctly.
  RETURN_IF_ERROR(owner_block_parse(&owner_page[0],
                                    /*check_only=*/kHardenedBoolTrue, NULL,
                                    NULL));
  ownership_seal_page(/*page=*/0);

  // Since this code should only execute when the ownership state is unknown, we
  // can thunk the ownership state to LockedOwner.
  bootdata->ownership_state = kOwnershipStateLockedOwner;

  // Write the configuration to page 0.
  OT_DISCARD(flash_ctrl_info_erase(&kFlashCtrlInfoPageOwnerSlot0,
                                   kFlashCtrlEraseTypePage));
  OT_DISCARD(flash_ctrl_info_write(&kFlashCtrlInfoPageOwnerSlot0, 0,
                                   sizeof(owner_page[0]) / sizeof(uint32_t),
                                   &owner_page[0]));
  owner_page_valid[0] = kOwnerPageStatusSealed;

  OT_DISCARD(boot_data_write(bootdata));
  dbg_printf("sku_creator_owner_init: saved to flash\r\n");
  return kErrorOk;
}
