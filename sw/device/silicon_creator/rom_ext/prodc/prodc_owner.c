// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom_ext/prodc/prodc_owner.h"

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
 * ownership.c, thus allowing existing prodc chips without an ownership
 * configuration to receive their ownership config simply installing the latest
 * ROM_EXT.
 */
rom_error_t sku_creator_owner_init(boot_data_t *bootdata,
                                   owner_config_t *config,
                                   owner_application_keyring_t *keyring) {
  const owner_key_t *owner = &((const owner_block_t *)prodc_owner)->owner_key;
  uint32_t config_version =
      ((const owner_block_t *)prodc_owner)->config_version;
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
  memcpy(&owner_page[0], prodc_owner, sizeof(prodc_owner));

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
