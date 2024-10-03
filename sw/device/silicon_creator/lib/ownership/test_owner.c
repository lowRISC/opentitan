// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/dbg_print.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/ownership/keys/fake/activate_ecdsa_p256.h"
#include "sw/device/silicon_creator/lib/ownership/keys/fake/app_dev_ecdsa_p256.h"
#include "sw/device/silicon_creator/lib/ownership/keys/fake/app_prod_ecdsa_p256.h"
#include "sw/device/silicon_creator/lib/ownership/keys/fake/app_test_ecdsa_p256.h"
#include "sw/device/silicon_creator/lib/ownership/keys/fake/owner_ecdsa_p256.h"
#include "sw/device/silicon_creator/lib/ownership/keys/fake/unlock_ecdsa_p256.h"
#include "sw/device/silicon_creator/lib/ownership/owner_block.h"
#include "sw/device/silicon_creator/lib/ownership/ownership.h"
#include "sw/device/silicon_creator/lib/ownership/ownership_key.h"

/*
 * This module overrides the weak `sku_creator_owner_init` symbol in
 * ownership.c, thus allowing FPGA builds to boot in the `LockedOwner` state
 * with a valid set of keys.
 */

// NOTE: if you update this version number, you must also update the version
// number in the test library `sw/host/tests/ownership/transfer_lib.rs`.
#define TEST_OWNER_CONFIG_VERSION 1

#ifndef TEST_OWNER_UPDATE_MODE
#define TEST_OWNER_UPDATE_MODE kOwnershipUpdateModeOpen
#endif

rom_error_t sku_creator_owner_init(boot_data_t *bootdata,
                                   owner_config_t *config,
                                   owner_application_keyring_t *keyring) {
  owner_key_t owner = (owner_key_t){
      // Although this is an ECDSA key, we initialize the `raw` member of the
      // union to zero-initialize the unused space.
      .raw = OWNER_ECDSA_P256};
  ownership_state_t state = bootdata->ownership_state;

  if (state == kOwnershipStateUnlockedSelf ||
      state == kOwnershipStateUnlockedAny ||
      state == kOwnershipStateUnlockedEndorsed) {
    // Nothing to do when in an unlocked state.
    return kErrorOk;
  } else if (state == kOwnershipStateLockedOwner) {
    if (hardened_memeq(owner.raw, owner_page[0].owner_key.raw,
                       ARRAYSIZE(owner.raw)) != kHardenedBoolTrue ||
        TEST_OWNER_CONFIG_VERSION <= owner_page[0].config_version) {
      // Different owner or already newest config version; nothing to do.
      return kErrorOk;
    }
  } else {
    // State is an unknown value, which is the same as kOwnershipStateRecovery.
    // We'll not return, thus allowing the owner config below to be programmed
    // into flash.
  }

  owner_page[0].header.tag = kTlvTagOwner;
  owner_page[0].header.length = 2048;
  owner_page[0].struct_version = 0;
  owner_page[0].sram_exec_mode = kOwnerSramExecModeDisabledLocked;
  owner_page[0].ownership_key_alg = kOwnershipKeyAlgEcdsaP256;
  owner_page[0].config_version = TEST_OWNER_CONFIG_VERSION;
  owner_page[0].min_security_version_bl0 = UINT32_MAX;
  owner_page[0].update_mode = TEST_OWNER_UPDATE_MODE;
  owner_page[0].owner_key = owner;
  owner_page[0].activate_key = (owner_key_t){
      // Although this is an ECDSA key, we initialize the `raw` member of the
      // union to zero-initialize the unused space.
      .raw = ACTIVATE_ECDSA_P256};
  owner_page[0].unlock_key = (owner_key_t){
      // Although this is an ECDSA key, we initialize the `raw` member of the
      // union to zero-initialize the unused space.
      .raw = UNLOCK_ECDSA_P256};

  // TODO: we're temporarily using RSA keys.
  // We'll change these to ECDSA keys after the ECDSA changes from
  // master are merged.
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
              .ecdsa = APP_TEST_ECDSA_P256,
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
              .ecdsa = APP_DEV_ECDSA_P256,
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
              .ecdsa = APP_PROD_ECDSA_P256,
          },
  };

  // Fill the remainder of the data segment with the end tag (0x5a5a5a5a).
  app = (owner_application_key_t *)((uintptr_t)app + app->header.length);
  size_t len = (uintptr_t)(owner_page[0].data + sizeof(owner_page[0].data)) -
               (uintptr_t)app;
  memset(app, 0x5a, len);

  ownership_seal_page(/*page=*/0);
  memcpy(&owner_page[1], &owner_page[0], sizeof(owner_page[0]));

  // Since this module should only get linked in to FPGA builds, we can simply
  // thunk the ownership state to LockedOwner.
  bootdata->ownership_state = kOwnershipStateLockedOwner;

  // Write the configuration to both owner pages.
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
