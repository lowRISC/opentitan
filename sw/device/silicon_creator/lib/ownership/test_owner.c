// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/dbg_print.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/ownership/keys/fake/activate_ecdsa_p256.h"
#include "sw/device/silicon_creator/lib/ownership/keys/fake/app_dev_ecdsa_p256.h"
#include "sw/device/silicon_creator/lib/ownership/keys/fake/app_dev_key_rsa_3072_exp_f4.h"
#include "sw/device/silicon_creator/lib/ownership/keys/fake/app_prod_ecdsa_p256.h"
#include "sw/device/silicon_creator/lib/ownership/keys/fake/app_prod_key_rsa_3072_exp_f4.h"
#include "sw/device/silicon_creator/lib/ownership/keys/fake/app_test_ecdsa_p256.h"
#include "sw/device/silicon_creator/lib/ownership/keys/fake/app_test_key_rsa_3072_exp_f4.h"
#include "sw/device/silicon_creator/lib/ownership/keys/fake/owner_ecdsa_p256.h"
#include "sw/device/silicon_creator/lib/ownership/keys/fake/unlock_ecdsa_p256.h"
#include "sw/device/silicon_creator/lib/ownership/owner_block.h"
#include "sw/device/silicon_creator/lib/ownership/ownership.h"

/*
 * This module overrides the weak `test_owner_init` symbol in ownership.c, thus
 * allowing FPGA builds to boot in the `LockedOwner` state with a valid set of
 * keys.
 */

rom_error_t test_owner_init(boot_data_t *bootdata, owner_config_t *config,
                            owner_application_keyring_t *keyring) {
  bool flash_invalid = owner_page[0].header.tag == 0xFFFFFFFF &&
                       owner_page[1].header.tag == 0xFFFFFFFF;

  owner_page[0].header.tag = kTlvTagOwner;
  owner_page[0].header.length = 2048;
  owner_page[0].version = 0;
  owner_page[0].sram_exec_mode = kOwnerSramExecModeDisabledLocked;
  owner_page[0].ownership_key_alg = kOwnershipKeyAlgEcdsaP256;
  owner_page[0].owner_key = (owner_key_t){OWNER_ECDSA_P256};
  owner_page[0].activate_key = (owner_key_t){ACTIVATE_ECDSA_P256};
  owner_page[0].unlock_key = (owner_key_t){UNLOCK_ECDSA_P256};

  // TODO: we're temporarily using RSA keys.
  // We'll change these to ECDSA keys after the ECDSA changes from
  // master are merged.
  owner_application_key_t *app = (owner_application_key_t *)owner_page[0].data;
  app[0] = (owner_application_key_t){
      .header =
          {
              .tag = kTlvTagApplicationKey,
              .length = sizeof(owner_application_key_t),
          },
      .key_alg = kOwnershipKeyAlgRsa,
      .key_domain = kOwnerAppDomainTest,
      .key_diversifier = {0},
      .usage_constraint = 0,
      .data =
          {
              .rsa = APP_TEST_KEY_RSA_3072_EXP_F4,
          },
  };
  app[1] = (owner_application_key_t){
      .header =
          {
              .tag = kTlvTagApplicationKey,
              .length = sizeof(owner_application_key_t),
          },
      .key_alg = kOwnershipKeyAlgRsa,
      .key_domain = kOwnerAppDomainProd,
      .key_diversifier = {0},
      .usage_constraint = 0,
      .data =
          {
              .rsa = APP_PROD_KEY_RSA_3072_EXP_F4,
          },
  };

  app = &app[2];
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

  ownership_page_seal(/*page=*/0);

  RETURN_IF_ERROR(owner_block_parse(&owner_page[0], config, keyring));
  RETURN_IF_ERROR(owner_block_flash_apply(config->flash, kBootSlotA,
                                          bootdata->primary_bl0_slot));
  RETURN_IF_ERROR(owner_block_flash_apply(config->flash, kBootSlotB,
                                          bootdata->primary_bl0_slot));
  RETURN_IF_ERROR(owner_block_info_apply(config->info));

  // Since this module should only get linked in to FPGA builds, we can simply
  // thunk the ownership state to LockedOwner.
  bootdata->ownership_state = kOwnershipStateLockedOwner;
  if (flash_invalid) {
    OT_DISCARD(flash_ctrl_info_erase(&kFlashCtrlInfoPageOwnerSlot0,
                                     kFlashCtrlEraseTypePage));
    OT_DISCARD(flash_ctrl_info_write(&kFlashCtrlInfoPageOwnerSlot0, 0,
                                     sizeof(owner_page[0]) / sizeof(uint32_t),
                                     &owner_page[0]));
    OT_DISCARD(boot_data_write(bootdata));
    dbg_printf("test_owner_init: flash\r\n");
  } else {
    dbg_printf("test_owner_init: ram\r\n");
  }
  return kErrorOk;
}
