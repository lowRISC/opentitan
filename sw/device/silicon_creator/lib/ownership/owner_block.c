// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/ownership/owner_block.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/base/chip.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "hw/top/flash_ctrl_regs.h"

// RAM copy of the owner INFO pages from flash.
owner_block_t owner_page[2];
owner_page_status_t owner_page_valid[2];

enum {
  kFlashBankSize = FLASH_CTRL_PARAM_REG_PAGES_PER_BANK,
  kFlashPageSize = FLASH_CTRL_PARAM_BYTES_PER_PAGE,
  kFlashTotalSize = 2 * kFlashBankSize,

  kRomExtSizeInPages = CHIP_ROM_EXT_SIZE_MAX / kFlashPageSize,
  kRomExtAStart = 0 / kFlashPageSize,
  kRomExtAEnd = kRomExtAStart + kRomExtSizeInPages,
  kRomExtBStart = kFlashBankSize + kRomExtAStart,
  kRomExtBEnd = kRomExtBStart + kRomExtSizeInPages,

  kRomExtRegions = 2,
  kProtectSlots = 8,
};

hardened_bool_t owner_block_newversion_mode(void) {
  if (owner_page_valid[0] == kOwnerPageStatusSealed &&
      (owner_page[0].update_mode == kOwnershipUpdateModeNewVersion ||
       owner_page[0].update_mode == kOwnershipUpdateModeSelfVersion)) {
    return kHardenedBoolTrue;
  }
  return kHardenedBoolFalse;
}

hardened_bool_t owner_block_page1_valid_for_transfer(boot_data_t *bootdata) {
  if (bootdata->ownership_state == kOwnershipStateLockedOwner &&
      owner_page_valid[1] == kOwnerPageStatusSealed) {
    return kHardenedBoolTrue;
  }
  if (owner_page_valid[1] == kOwnerPageStatusSigned) {
    hmac_digest_t digest;
    switch (bootdata->ownership_state) {
      case kOwnershipStateUnlockedAny:
        // In UnlockedAny, any valid (signed) Owner Page 1 is acceptable.
        return kHardenedBoolTrue;
      case kOwnershipStateUnlockedSelf:
        // In UnlockedSelf, the owner key must be the same.  If not,
        // skip parsing of Owner Page 1.
        if (hardened_memeq(
                owner_page[0].owner_key.raw, owner_page[1].owner_key.raw,
                ARRAYSIZE(owner_page[0].owner_key.raw)) == kHardenedBoolTrue) {
          return kHardenedBoolTrue;
        }
        break;
      case kOwnershipStateUnlockedEndorsed:
        // In UnlockedEndorsed, the owner key must match the key endorsed by the
        // next_owner field in bootdata.  If not, skip parsing owner page 1.
        hmac_sha256(owner_page[1].owner_key.raw,
                    sizeof(owner_page[1].owner_key.raw), &digest);
        if (hardened_memeq(bootdata->next_owner, digest.digest,
                           ARRAYSIZE(digest.digest)) == kHardenedBoolTrue) {
          return kHardenedBoolTrue;
        }
        break;
      default:
          /* nothing */;
    }
  }
  return kHardenedBoolFalse;
}

void owner_config_default(owner_config_t *config) {
  // Use a bogus pointer value to avoid the all-zeros pattern of NULL.
  config->flash = (const owner_flash_config_t *)kHardenedBoolFalse;
  config->info = (const owner_flash_info_config_t *)kHardenedBoolFalse;
  config->rescue = (const owner_rescue_config_t *)kHardenedBoolFalse;
  config->sram_exec = kOwnerSramExecModeDisabledLocked;
}

rom_error_t owner_block_parse(const owner_block_t *block,
                              hardened_bool_t check_only,
                              owner_config_t *config,
                              owner_application_keyring_t *keyring) {
  if (block->header.tag != kTlvTagOwner)
    return kErrorOwnershipInvalidTag;
  if (block->header.length != sizeof(owner_block_t))
    return kErrorOwnershipInvalidTagLength;
  if (block->header.version.major != 0)
    return kErrorOwnershipOWNRVersion;

  if (check_only == kHardenedBoolFalse) {
    owner_config_default(config);
    config->sram_exec = block->sram_exec_mode;
  }

  uint32_t remain = sizeof(block->data);
  uint32_t offset = 0;
  while (remain) {
    const tlv_header_t *item = (const tlv_header_t *)(block->data + offset);
    if (item->tag == kTlvTagNotPresent) {
      break;
    }
    if (item->length < 8 || item->length > remain || item->length % 4 != 0) {
      return kErrorOwnershipInvalidTagLength;
    }
    remain -= item->length;
    offset += item->length;
    uint32_t tag = item->tag;
    switch (launder32(item->tag)) {
      case kTlvTagApplicationKey:
        HARDENED_CHECK_EQ(tag, kTlvTagApplicationKey);
        if (item->version.major != 0)
          return kErrorOwnershipAPPKVersion;

        if (check_only == kHardenedBoolFalse) {
          if (keyring->length < ARRAYSIZE(keyring->key)) {
            keyring->key[keyring->length++] =
                (const owner_application_key_t *)item;
          }
        }
        break;
      case kTlvTagFlashConfig:
        HARDENED_CHECK_EQ(tag, kTlvTagFlashConfig);
        if (item->version.major != 0)
          return kErrorOwnershipFLSHVersion;
        if (check_only == kHardenedBoolFalse) {
          if ((hardened_bool_t)config->flash != kHardenedBoolFalse)
            return kErrorOwnershipDuplicateItem;
          config->flash = (const owner_flash_config_t *)item;
        } else {
          HARDENED_RETURN_IF_ERROR(
              owner_block_flash_check((const owner_flash_config_t *)item));
        }
        break;
      case kTlvTagInfoConfig:
        HARDENED_CHECK_EQ(tag, kTlvTagInfoConfig);
        if (item->version.major != 0)
          return kErrorOwnershipINFOVersion;
        if (check_only == kHardenedBoolFalse) {
          if ((hardened_bool_t)config->info != kHardenedBoolFalse)
            return kErrorOwnershipDuplicateItem;
          config->info = (const owner_flash_info_config_t *)item;
        }
        break;
      case kTlvTagRescueConfig:
        HARDENED_CHECK_EQ(tag, kTlvTagRescueConfig);
        if (item->version.major != 0)
          return kErrorOwnershipRESQVersion;
        if (check_only == kHardenedBoolFalse) {
          if ((hardened_bool_t)config->rescue != kHardenedBoolFalse)
            return kErrorOwnershipDuplicateItem;
          config->rescue = (const owner_rescue_config_t *)item;
        }
        break;
      default:
        return kErrorOwnershipInvalidTag;
    }
  }
  return kErrorOk;
}

// These functions aren't defined in owner_block.h because they aren't meant
// to be public APIs.  They aren't static so we can access the symbols in the
// unit test program.

// Checks if the half-open range [start..end) overlaps with the ROM_EXT region.
// The RomExt_Start/End constants are also expressed as half-open ranges.
hardened_bool_t rom_ext_flash_overlap(uint32_t start, uint32_t end) {
  return (start < kRomExtAEnd && end > kRomExtAStart) ||
                 (start < kRomExtBEnd && end > kRomExtBStart)
             ? kHardenedBoolTrue
             : kHardenedBoolFalse;
}

// Checks if the half-open range [start..end) is exclusively within the ROM_EXT
// region. The RomExt_Start/End constants are also expressed as half-open
// ranges.
hardened_bool_t rom_ext_flash_exclusive(uint32_t start, uint32_t end) {
  return (kRomExtAStart <= start && start < kRomExtAEnd &&
          kRomExtAStart < end && end <= kRomExtAEnd) ||
                 (kRomExtBStart <= start && start < kRomExtBEnd &&
                  kRomExtBStart < end && end <= kRomExtBEnd)
             ? kHardenedBoolTrue
             : kHardenedBoolFalse;
}

rom_error_t owner_block_flash_check(const owner_flash_config_t *flash) {
  size_t len = (flash->header.length - sizeof(owner_flash_config_t)) /
               sizeof(owner_flash_region_t);
  if (len > kProtectSlots - kRomExtRegions) {
    return kErrorOwnershipFlashConfigLength;
  }

  const owner_flash_region_t *config = flash->config;
  uint32_t crypt = 0;
  for (size_t i = 0; i < len; ++i, ++config, crypt += 0x11111111) {
    uint32_t start = config->start;
    uint32_t end = start + config->size;
    if (end > kFlashTotalSize) {
      return kErrorOwnershipFlashConfigBounds;
    }
    // When checking the flash configuration, a region is a ROM_EXT region if
    // it overlaps the ROM_EXT bounds.  It is an error to accept a new config
    // with a flash region that overlaps the ROM_EXT.
    if (rom_ext_flash_overlap(start, end) == kHardenedBoolTrue) {
      return kErrorOwnershipFlashConfigRomExt;
    }
  }
  return kErrorOk;
}

rom_error_t owner_block_flash_apply(const owner_flash_config_t *flash,
                                    uint32_t config_side,
                                    uint32_t owner_lockdown) {
  if ((hardened_bool_t)flash == kHardenedBoolFalse)
    return kErrorOk;

  // TODO: Hardening: lockdown should be one of kBootSlotA, kBootSlotB or
  // kHardenedBoolFalse.
  uint32_t start = config_side == kBootSlotA   ? 0
                   : config_side == kBootSlotB ? kFlashBankSize
                                               : 0xFFFFFFFF;
  uint32_t end = config_side == kBootSlotA   ? kFlashBankSize
                 : config_side == kBootSlotB ? 2 * kFlashBankSize
                                             : 0;
  size_t len = (flash->header.length - sizeof(owner_flash_config_t)) /
               sizeof(owner_flash_region_t);
  if (len > kProtectSlots - kRomExtRegions) {
    return kErrorOwnershipFlashConfigLength;
  }

  const owner_flash_region_t *config = flash->config;
  uint32_t crypt = 0;
  for (size_t i = 0; i < len; ++i, ++config, crypt += 0x11111111) {
    if (config->start >= start && config->start + config->size <= end) {
      uint32_t val = config->properties ^ crypt;
      flash_ctrl_cfg_t cfg = {
          .scrambling = bitfield_field32_read(val, FLASH_CONFIG_SCRAMBLE),
          .ecc = bitfield_field32_read(val, FLASH_CONFIG_ECC),
          .he = bitfield_field32_read(val, FLASH_CONFIG_HIGH_ENDURANCE),
      };
      val = config->access ^ crypt;
      flash_ctrl_perms_t perm = {
          .read = bitfield_field32_read(val, FLASH_CONFIG_READ),
          .write = bitfield_field32_read(val, FLASH_CONFIG_PROGRAM),
          .erase = bitfield_field32_read(val, FLASH_CONFIG_ERASE),
      };

      uint32_t pwp =
          bitfield_field32_read(val, FLASH_CONFIG_PROTECT_WHEN_PRIMARY);
      hardened_bool_t lock =
          bitfield_field32_read(val, FLASH_CONFIG_LOCK) != kMultiBitBool4False
              ? kHardenedBoolTrue
              : kHardenedBoolFalse;
      uint32_t region_start = config->start;
      uint32_t region_end = region_start + config->size;

      // When applying the flash configuration, a region is a ROM_EXT region if
      // it is exclusively within the ROM_EXT bounds.  This sets the creator
      // the lockdown policy for a region that is exclusively the creator
      // region.
      if (rom_ext_flash_exclusive(region_start, region_end) ==
          kHardenedBoolTrue) {
        // Flash region is a ROM_EXT region.  Do nothing.
        // Some early configurations explicitly set parameters for the ROM_EXT
        // region.  We ignore these regions in favor of the ROM_EXT setting
        // its own protection parameters.
        continue;
      } else {
        // Flash region is an owner region.
        // If the config_side is the same as the owner lockdown side, and
        // protect_when_primary is requested, deny write/erase to the region.
        if (config_side == owner_lockdown && pwp != kMultiBitBool4False) {
          perm.write = kMultiBitBool4False;
          perm.erase = kMultiBitBool4False;
        }
        // If we aren't in a lockdown state, then do not lock the region
        // configuration via the flash_ctrl regwen bits.
        if (owner_lockdown == kHardenedBoolFalse) {
          lock = kHardenedBoolFalse;
        }
      }
      flash_ctrl_data_region_protect(kRomExtRegions + i, config->start,
                                     config->size, perm, cfg, lock);
    }
  }
  return kErrorOk;
}

static inline hardened_bool_t is_owner_page(const owner_info_page_t *config) {
  // On earlgrey_a1, in banks 0 and 1, pages 5-8 (inclusive) are reserved
  // for the owner.
  if (config->page >= 5 && config->page <= 8) {
    return kHardenedBoolTrue;
  }
  return kHardenedBoolFalse;
}

rom_error_t owner_block_info_apply(const owner_flash_info_config_t *info) {
  if ((hardened_bool_t)info == kHardenedBoolFalse)
    return kErrorOk;
  size_t len = (info->header.length - sizeof(owner_flash_info_config_t)) /
               sizeof(owner_info_page_t);
  const owner_info_page_t *config = info->config;
  uint32_t crypt = 0;
  for (size_t i = 0; i < len; ++i, ++config, crypt += 0x11111111) {
    if (is_owner_page(config) == kHardenedBoolTrue) {
      flash_ctrl_info_page_t page = {
          .base_addr = config->bank * FLASH_CTRL_PARAM_BYTES_PER_BANK +
                       config->page * FLASH_CTRL_PARAM_BYTES_PER_PAGE,
          .cfg_wen_offset =
              config->page * sizeof(uint32_t) +
              (config->bank == 0 ? FLASH_CTRL_BANK0_INFO0_REGWEN_0_REG_OFFSET
                                 : FLASH_CTRL_BANK1_INFO0_REGWEN_0_REG_OFFSET),
          .cfg_offset = config->page * sizeof(uint32_t) +
                        (config->bank == 0
                             ? FLASH_CTRL_BANK0_INFO0_PAGE_CFG_0_REG_OFFSET
                             : FLASH_CTRL_BANK1_INFO0_PAGE_CFG_0_REG_OFFSET),
      };

      uint32_t val = config->properties ^ crypt;
      flash_ctrl_cfg_t cfg = {
          .scrambling = bitfield_field32_read(val, FLASH_CONFIG_SCRAMBLE),
          .ecc = bitfield_field32_read(val, FLASH_CONFIG_ECC),
          .he = bitfield_field32_read(val, FLASH_CONFIG_HIGH_ENDURANCE),
      };
      flash_ctrl_info_cfg_set(&page, cfg);

      val = config->access ^ crypt;
      flash_ctrl_perms_t perm = {
          .read = bitfield_field32_read(val, FLASH_CONFIG_READ),
          .write = bitfield_field32_read(val, FLASH_CONFIG_PROGRAM),
          .erase = bitfield_field32_read(val, FLASH_CONFIG_ERASE),
      };
      flash_ctrl_info_perms_set(&page, perm);
    }
  }
  return kErrorOk;
}

rom_error_t owner_keyring_find_key(const owner_application_keyring_t *keyring,
                                   uint32_t key_id, size_t *index) {
  for (size_t i = 0; i < keyring->length; ++i) {
    uint32_t id = keyring->key[i]->data.id;
    if ((keyring->key[i]->key_alg & kOwnershipKeyAlgCategoryMask) ==
        kOwnershipKeyAlgCategoryHybrid) {
      // The ID of a hybrid key is the xor of the IDs of each key.
      id ^= keyring->key[i]->data.hybrid.spx.data[0];
    }
    if (id == key_id) {
      *index = i;
      return kErrorOk;
    }
  }
  return kErrorOwnershipKeyNotFound;
}

size_t owner_block_key_page(const owner_application_key_t *key) {
  // The key pointer must point to a memory address on one of the two owner
  // pages.
  HARDENED_CHECK_GT((uintptr_t)key, (uintptr_t)&owner_page[0]);
  HARDENED_CHECK_LT((uintptr_t)key,
                    (uintptr_t)&owner_page[ARRAYSIZE(owner_page)]);
  return (uintptr_t)key < (uintptr_t)&owner_page[1] ? 0 : 1;
}

hardened_bool_t owner_rescue_command_allowed(
    const owner_rescue_config_t *rescue, uint32_t command) {
  // If no rescue configuration is supplied in the owner config, then all rescue
  // commands are allowed.
  if ((hardened_bool_t)rescue == kHardenedBoolFalse)
    return kHardenedBoolTrue;

  hardened_bool_t allowed = kHardenedBoolFalse;
  size_t length = (rescue->header.length - sizeof(*rescue)) / sizeof(uint32_t);
  for (size_t i = 0; i < length; ++i) {
    if (command == rescue->command_allow[i]) {
      allowed = kHardenedBoolTrue;
    }
  }
  return allowed;
}

void owner_block_measurement(size_t page, hmac_digest_t *measurement) {
  HARDENED_CHECK_LT(page, ARRAYSIZE(owner_page));
  // Digest of the contents of the owner page, not including the signature or
  // the seal.
  size_t len = offsetof(owner_block_t, signature);
  hmac_sha256(&owner_page[page], len, measurement);
}
