// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/dbg_print.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/ownership/owner_block.h"
#include "sw/device/silicon_creator/lib/ownership/ownership.h"
#include "sw/device/silicon_creator/lib/ownership/ownership_key.h"
#include "sw/device/silicon_creator/rom_ext/proda/keys/appkey_dev_0.h"
#include "sw/device/silicon_creator/rom_ext/proda/keys/appkey_prod_0.h"
#include "sw/device/silicon_creator/rom_ext/proda/keys/appkey_test_0.h"
#include "sw/device/silicon_creator/rom_ext/proda/keys/ownership_activate_key.h"
#include "sw/device/silicon_creator/rom_ext/proda/keys/ownership_owner_key.h"
#include "sw/device/silicon_creator/rom_ext/proda/keys/ownership_unlock_key.h"

/*
 * This module overrides the weak `sku_creator_owner_init` symbol in
 * ownership.c, thus allowing existing proda chips without an ownership
 * configuration to receive their ownership config simply installing the latest
 * ROM_EXT.
 */

#define PRODA_OWNER_CONFIG_VERSION 1

rom_error_t sku_creator_owner_init(boot_data_t *bootdata,
                                   owner_config_t *config,
                                   owner_application_keyring_t *keyring) {
  owner_key_t owner = (owner_key_t){
      // Although this is an ECDSA key, we initialize the `raw` member of the
      // union to zero-initialize the unused space.
      .raw = OWNERSHIP_OWNER_KEY};
  ownership_state_t state = bootdata->ownership_state;

  if (state == kOwnershipStateUnlockedSelf ||
      state == kOwnershipStateUnlockedAny ||
      state == kOwnershipStateUnlockedEndorsed) {
    // Nothing to do when in an unlocked state.
    return kErrorOk;
  } else if (state == kOwnershipStateLockedOwner) {
    if (hardened_memeq(owner.raw, owner_page[0].owner_key.raw,
                       ARRAYSIZE(owner.raw)) != kHardenedBoolTrue ||
        PRODA_OWNER_CONFIG_VERSION <= owner_page[0].config_version) {
      // Different owner or already newest config version; nothing to do.
      return kErrorOk;
    }
  } else {
    // State is an unknown value, which is the same as kOwnershipStateRecovery.
    // We'll not return, thus allowing the owner config below to be programmed
    // into flash.
  }

  memset(&owner_page[0], 0, sizeof(owner_page[0]));
  owner_page[0].header.tag = kTlvTagOwner;
  owner_page[0].header.length = 2048;
  owner_page[0].header.version = (struct_version_t){0, 0};
  owner_page[0].config_version = PRODA_OWNER_CONFIG_VERSION;
  owner_page[0].sram_exec_mode = kOwnerSramExecModeDisabledLocked;
  owner_page[0].ownership_key_alg = kOwnershipKeyAlgEcdsaP256;
  owner_page[0].update_mode = kOwnershipUpdateModeOpen;
  owner_page[0].min_security_version_bl0 = UINT32_MAX;
  owner_page[0].owner_key = owner;
  owner_page[0].activate_key = (owner_key_t){
      // Although this is an ECDSA key, we initialize the `raw` member of the
      // union to zero-initialize the unused space.
      .raw = OWNERSHIP_ACTIVATE_KEY};
  owner_page[0].unlock_key = (owner_key_t){
      // Although this is an ECDSA key, we initialize the `raw` member of the
      // union to zero-initialize the unused space.
      .raw = OWNERSHIP_UNLOCK_KEY};

  owner_application_key_t *app = (owner_application_key_t *)owner_page[0].data;
  *app = (owner_application_key_t){
      .header =
          {
              .tag = kTlvTagApplicationKey,
              .length = kTlvLenApplicationKeyEcdsa,
          },
      .key_alg = kOwnershipKeyAlgEcdsaP256,
      .key_domain = kOwnerAppDomainTest,
      .key_diversifier = {0},
      .usage_constraint = 0,
      .data =
          {
              .ecdsa = APPKEY_TEST_0,
          },
  };

  app = (owner_application_key_t *)((uintptr_t)app + app->header.length);
  *app = (owner_application_key_t){
      .header =
          {
              .tag = kTlvTagApplicationKey,
              .length = kTlvLenApplicationKeyEcdsa,
          },
      .key_alg = kOwnershipKeyAlgEcdsaP256,
      .key_domain = kOwnerAppDomainProd,
      .key_diversifier = {0},
      .usage_constraint = 0,
      .data =
          {
              .ecdsa = APPKEY_PROD_0,
          },
  };

  app = (owner_application_key_t *)((uintptr_t)app + app->header.length);
  *app = (owner_application_key_t){
      .header =
          {
              .tag = kTlvTagApplicationKey,
              .length = kTlvLenApplicationKeyEcdsa,
          },
      .key_alg = kOwnershipKeyAlgEcdsaP256,
      .key_domain = kOwnerAppDomainDev,
      .key_diversifier = {0},
      .usage_constraint = 0,
      .data =
          {
              .ecdsa = APPKEY_DEV_0,
          },
  };

  // Fill the remainder of the data segment with the end tag (0x5a5a5a5a).
  app = (owner_application_key_t *)((uintptr_t)app + app->header.length);
  size_t len = (uintptr_t)(owner_page[0].data + sizeof(owner_page[0].data)) -
               (uintptr_t)app;
  memset(app, 0x5a, len);

  ownership_seal_page(/*page=*/0);
  memcpy(&owner_page[1], &owner_page[0], sizeof(owner_page[0]));

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
