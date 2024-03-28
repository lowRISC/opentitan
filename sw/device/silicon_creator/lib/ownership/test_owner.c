// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/dbg_print.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/ownership/keys/fake/activate_ecdsa_p256.h"
#include "sw/device/silicon_creator/lib/ownership/keys/fake/app_dev_key_rsa_3072_exp_f4.h"
#include "sw/device/silicon_creator/lib/ownership/keys/fake/app_prod_key_rsa_3072_exp_f4.h"
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
  owner_page[0].header.tag = kTlvTagOwner;
  owner_page[0].header.length = 2048;
  owner_page[0].version = 0;
  owner_page[0].sram_exec_mode = kOwnerSramExecModeDisabled;
  owner_page[0].ownership_key_alg = kOwnershipKeyAlgEcdsaP256;
  owner_page[0].owner_key = (owner_key_t){OWNER_ECDSA_P256};
  owner_page[0].activate_key = (owner_key_t){ACTIVATE_ECDSA_P256};
  owner_page[0].unlock_key = (owner_key_t){UNLOCK_ECDSA_P256};

  // Fill the data segment with the end tag (0x5a5a5a5a).
  memset(owner_page[0].data, 0x5a, sizeof(owner_page[0].data));

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
      .key_domain = kOwnerAppDomainDev,
      .key_diversifier = {0},
      .usage_constraint = 0,
      .data =
          {
              .rsa = APP_DEV_KEY_RSA_3072_EXP_F4,
          },
  };
  app[2] = (owner_application_key_t){
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

  ownership_page_seal(/*page=*/0);

  RETURN_IF_ERROR(owner_block_parse(&owner_page[0], config, keyring));
  RETURN_IF_ERROR(owner_block_flash_apply(config->flash, kBootSlotA,
                                          bootdata->primary_bl0_slot));
  RETURN_IF_ERROR(owner_block_flash_apply(config->flash, kBootSlotB,
                                          bootdata->primary_bl0_slot));
  RETURN_IF_ERROR(owner_block_info_apply(config->info));
  // TODO: apply SRAM exec config
  // TODO: apply rescue config

  // Since this module should only get linked in to FPGA builds, we can simply
  // thunk the ownership state to LockedOwner.
  bootdata->ownership_state = kOwnershipStateLockedOwner;
  dbg_printf("Test owner initialized\r\n");
  return kErrorOk;
}
