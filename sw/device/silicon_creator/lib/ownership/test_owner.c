// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_msg.h"
#include "sw/device/silicon_creator/lib/dbg_print.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/ownership/datatypes.h"
#include "sw/device/silicon_creator/lib/ownership/keys/fake/activate_ecdsa_p256.h"
#include "sw/device/silicon_creator/lib/ownership/keys/fake/activate_spx.h"
#include "sw/device/silicon_creator/lib/ownership/keys/fake/app_dev_ecdsa_p256.h"
#include "sw/device/silicon_creator/lib/ownership/keys/fake/app_dev_spx.h"
#include "sw/device/silicon_creator/lib/ownership/keys/fake/app_prod_ecdsa_p256.h"
#include "sw/device/silicon_creator/lib/ownership/keys/fake/app_prod_spx.h"
#include "sw/device/silicon_creator/lib/ownership/keys/fake/app_test_ecdsa_p256.h"
#include "sw/device/silicon_creator/lib/ownership/keys/fake/owner_ecdsa_p256.h"
#include "sw/device/silicon_creator/lib/ownership/keys/fake/owner_spx.h"
#include "sw/device/silicon_creator/lib/ownership/keys/fake/unlock_ecdsa_p256.h"
#include "sw/device/silicon_creator/lib/ownership/keys/fake/unlock_spx.h"
#include "sw/device/silicon_creator/lib/ownership/owner_block.h"
#include "sw/device/silicon_creator/lib/ownership/ownership.h"
#include "sw/device/silicon_creator/lib/ownership/ownership_key.h"
#include "sw/device/silicon_creator/lib/rescue/rescue.h"

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

#if defined(TEST_OWNER_KEY_ALG_HYBRID_SPX_PURE) || \
    defined(TEST_OWNER_KEY_ALG_HYBRID_SPX_PREHASH)
#ifdef TEST_OWNER_KEY_ALG_HYBRID_SPX_PURE
#define TEST_OWNER_KEY_ALG kOwnershipKeyAlgHybridSpxPure
#endif
#ifdef TEST_OWNER_KEY_ALG_HYBRID_SPX_PREHASH
#define TEST_OWNER_KEY_ALG kOwnershipKeyAlgHybridSpxPrehash
#endif
#define OWNER_KEYDATA                                        \
  (owner_keydata_t) {                                        \
    .hybrid = {.ecdsa = OWNER_ECDSA_P256, .spx = OWNER_SPX } \
  }
#define ACTIVATE_KEYDATA                                           \
  (owner_keydata_t) {                                              \
    .hybrid = {.ecdsa = ACTIVATE_ECDSA_P256, .spx = ACTIVATE_SPX } \
  }
#define UNLOCK_KEYDATA                                         \
  (owner_keydata_t) {                                          \
    .hybrid = {.ecdsa = UNLOCK_ECDSA_P256, .spx = UNLOCK_SPX } \
  }
#endif

#if defined(TEST_OWNER_KEY_ALG_SPX_PURE) || \
    defined(TEST_OWNER_KEY_ALG_SPX_PREHASH)
#ifdef TEST_OWNER_KEY_ALG_SPX_PURE
#define TEST_OWNER_KEY_ALG kOwnershipKeyAlgSpxPure
#endif
#ifdef TEST_OWNER_KEY_ALG_HYBRID_SPX_PREHASH
#define TEST_OWNER_KEY_ALG kOwnershipKeyAlgSpxPrehash
#endif
#define OWNER_KEYDATA \
  (owner_keydata_t) { .spx = OWNER_SPX }
#define ACTIVATE_KEYDATA \
  (owner_keydata_t) { .spx = ACTIVATE_SPX }
#define UNLOCK_KEYDATA \
  (owner_keydata_t) { .spx = UNLOCK_SPX }
#endif

#if defined(TEST_OWNER_KEY_ALG_CORRUPTED)
#ifdef TEST_OWNER_KEY_ALG_CORRUPTED
#define TEST_OWNER_KEY_ALG 0x0
#define OWNER_KEYDATA \
  (owner_keydata_t) { .ecdsa = OWNER_ECDSA_P256 }
#define ACTIVATE_KEYDATA \
  (owner_keydata_t) { .ecdsa = ACTIVATE_ECDSA_P256 }
#define UNLOCK_KEYDATA \
  (owner_keydata_t) { .ecdsa = UNLOCK_ECDSA_P256 }
#endif
#endif

#ifndef TEST_OWNER_KEY_ALG
#define TEST_OWNER_KEY_ALG kOwnershipKeyAlgEcdsaP256
#define OWNER_KEYDATA \
  (owner_keydata_t) { .ecdsa = OWNER_ECDSA_P256 }
#define ACTIVATE_KEYDATA \
  (owner_keydata_t) { .ecdsa = ACTIVATE_ECDSA_P256 }
#define UNLOCK_KEYDATA \
  (owner_keydata_t) { .ecdsa = UNLOCK_ECDSA_P256 }
#endif

#ifndef TEST_OWNERSHIP_STATE
#define TEST_OWNERSHIP_STATE kOwnershipStateLockedOwner
#endif

#ifndef TEST_OWNER_SRAM_EXEC_MODE
#define TEST_OWNER_SRAM_EXEC_MODE kOwnerSramExecModeDisabledLocked
#endif

#ifndef TEST_OWNER_BOOT_SVC_AFTER_WAKEUP
#define TEST_OWNER_BOOT_SVC_AFTER_WAKEUP kHardenedBoolFalse
#endif

// The following preprocessor symbols are only relevant when
// WITH_RESCUE_PROTOCOL is defined.
#ifndef WITH_RESCUE_MISC_GPIO_PARAM
#define WITH_RESCUE_MISC_GPIO_PARAM 0
#endif
#ifndef WITH_RESCUE_INDEX
#define WITH_RESCUE_INDEX 0
#endif
#ifndef WITH_RESCUE_TIMEOUT
#define WITH_RESCUE_TIMEOUT 0 /* No timeout, no enter-on-fail */
#endif
#ifndef WITH_RESCUE_TRIGGER
#define WITH_RESCUE_TRIGGER 1 /* default to UartBreak */
#endif
#ifndef WITH_RESCUE_COMMAND_ALLOW
#define WITH_RESCUE_COMMAND_ALLOW                                            \
  kRescueModeBootLog, kRescueModeBootSvcRsp, kRescueModeBootSvcReq,          \
      kRescueModeOwnerBlock, kRescueModeOwnerPage0, kRescueModeOwnerPage1,   \
      kRescueModeOpenTitanID, kRescueModeFirmware, kRescueModeFirmwareSlotB, \
      kBootSvcEmptyReqType, kBootSvcNextBl0SlotReqType,                      \
      kBootSvcMinBl0SecVerReqType, kBootSvcOwnershipActivateReqType,         \
      kBootSvcOwnershipUnlockReqType,
#endif
#ifndef WITH_RESCUE_START
#define WITH_RESCUE_START (32)
#endif
#ifndef WITH_RESCUE_SIZE
#define WITH_RESCUE_SIZE (224)
#endif

rom_error_t sku_creator_owner_init(boot_data_t *bootdata) {
#ifdef TEST_FAULT_NO_OWNER
  return kErrorOwnershipNoOwner;
#endif

  owner_keydata_t owner = OWNER_KEYDATA;
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
  owner_page[0].header.version = (struct_version_t){0, 0};
  owner_page[0].config_version = TEST_OWNER_CONFIG_VERSION;
  owner_page[0].sram_exec_mode = TEST_OWNER_SRAM_EXEC_MODE;
  owner_page[0].boot_svc_after_wakeup = TEST_OWNER_BOOT_SVC_AFTER_WAKEUP;
  owner_page[0].ownership_key_alg = TEST_OWNER_KEY_ALG;
  owner_page[0].update_mode = TEST_OWNER_UPDATE_MODE;
  owner_page[0].min_security_version_bl0 = UINT32_MAX;
  owner_page[0].lock_constraint = 0;
  memset(owner_page[0].device_id, kLockConstraintNone,
         sizeof(owner_page[0].device_id));
  owner_page[0].owner_key = owner;
  owner_page[0].activate_key = ACTIVATE_KEYDATA;
  owner_page[0].unlock_key = UNLOCK_KEYDATA;

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

  app = (owner_application_key_t *)((uintptr_t)app + app->header.length);
  *app = (owner_application_key_t){
      .header =
          {
              .tag = kTlvTagApplicationKey,
              .length = kTlvLenApplicationKeyHybrid,
          },
      .key_alg = kOwnershipKeyAlgHybridSpxPure,
      .key_domain = kOwnerAppDomainProd,
      .key_diversifier = {0},
      .usage_constraint = 0,
      .data =
          {
              .hybrid =
                  {
                      .ecdsa = APP_PROD_ECDSA_P256,
                      .spx = APP_PROD_SPX,
                  },
          },
  };

  app = (owner_application_key_t *)((uintptr_t)app + app->header.length);
  *app = (owner_application_key_t){
      .header =
          {
              .tag = kTlvTagApplicationKey,
              .length = kTlvLenApplicationKeyHybrid,
          },
      .key_alg = kOwnershipKeyAlgHybridSpxPrehash,
      .key_domain = kOwnerAppDomainDev,
      .key_diversifier = {0},
      .usage_constraint = 0,
      .data =
          {
              .hybrid =
                  {
                      .ecdsa = APP_DEV_ECDSA_P256,
                      .spx = APP_DEV_SPX,
                  },
          },
  };

  uintptr_t end = (uintptr_t)app + app->header.length;
#ifdef WITH_RESCUE_PROTOCOL
  owner_rescue_config_t *rescue =
      (owner_rescue_config_t *)((uintptr_t)app + app->header.length);
  *rescue = (owner_rescue_config_t){
      .header =
          {
              .tag = kTlvTagRescueConfig,
              .length = sizeof(owner_rescue_config_t),
          },
      .protocol = WITH_RESCUE_PROTOCOL,
      .gpio = WITH_RESCUE_MISC_GPIO_PARAM,
      .timeout = WITH_RESCUE_TIMEOUT,
      .detect = (WITH_RESCUE_TRIGGER << 6) | WITH_RESCUE_INDEX,
      .start = WITH_RESCUE_START,
      .size = WITH_RESCUE_SIZE,
  };
  const uint32_t commands[] = {WITH_RESCUE_COMMAND_ALLOW};
  memcpy(&rescue->command_allow, commands, sizeof(commands));
  rescue->header.length += sizeof(commands);
  end = (uintptr_t)rescue + rescue->header.length;
#endif
#ifdef WITH_ISFB
  owner_flash_info_config_t *info = (owner_flash_info_config_t *)end;
  info->header = (tlv_header_t){
      .tag = kTlvTagInfoConfig,
      .length = sizeof(owner_flash_info_config_t) + sizeof(owner_info_page_t),
  };
  info->config[0] = (owner_info_page_t){
      .bank = 0,
      .page = 5,
      // Access: -erase, +program, +read.
      .access = 0x066,
      .properties = 0,
  };
  end = (uintptr_t)info + info->header.length;
  owner_isfb_config_t *isfb = (owner_isfb_config_t *)end;
  *isfb = (owner_isfb_config_t){
      .header =
          {
              .tag = kTlvTagIntegrationSpecificFirmwareBinding,
              .length = sizeof(owner_isfb_config_t),
          },
      .bank = 0,
      .page = 5,
      // erase extension present, node-locked and specific key domain.
      .erase_conditions = 0x666,
      .key_domain = kOwnerAppDomainProd,
      .product_words = 2,
  };
  end = (uintptr_t)isfb + isfb->header.length;
#endif
  // Fill the remainder of the data segment with the end tag (0x5a5a5a5a).
  size_t len = (uintptr_t)(owner_page[0].data + sizeof(owner_page[0].data)) -
               (uintptr_t)end;
  memset((void *)end, 0x5a, len);

#ifndef TEST_OWNER_DISABLE_OWNER_BLOCK_CHECK
  // Check that the owner_block will parse correctly.
  RETURN_IF_ERROR(owner_block_parse(&owner_page[0],
                                    /*check_only=*/kHardenedBoolTrue, NULL,
                                    NULL));
#endif
  ownership_seal_page(/*page=*/0);

  // Since this module should only get linked in to FPGA builds, we can simply
  // thunk the ownership state to LockedOwner.
  bootdata->ownership_state = TEST_OWNERSHIP_STATE;

  // Write the configuration to both owner page 0.  The next boot of the ROM_EXT
  // will make a redundant copyh in page 1.
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

#ifdef WITH_FALLBACK_OWNER

#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wgnu-flexible-array-initializer"
static const owner_rescue_config_t fallback_rescue_config = {
    .header =
        {
            .tag = kTlvTagRescueConfig,
            .length = sizeof(owner_rescue_config_t) + 1 * sizeof(uint32_t),
            .version = {0, 0},
        },
    .protocol = WITH_RESCUE_PROTOCOL,
    .gpio = WITH_RESCUE_MISC_GPIO_PARAM,
    .timeout = WITH_RESCUE_TIMEOUT,
    .detect = (WITH_RESCUE_TRIGGER << 6) | WITH_RESCUE_INDEX,
    .start = 32,
    .size = 224,
    .command_allow = {kRescueModeOpenTitanID},
};
#pragma clang diagnostic pop

void owner_config_default(owner_config_t *config) {
  owner_config_clear(config);
  config->rescue = &fallback_rescue_config;
  OT_DISCARD(owner_block_rescue_apply(config->rescue));
  dbg_printf("info: set fallback owner with customized settings\r\n");
}

#endif
