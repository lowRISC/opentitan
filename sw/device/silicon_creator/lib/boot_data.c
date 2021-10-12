// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/boot_data.h"

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/memory.h"
// TODO(#8777): Use silicon_creator flash_ctrl driver when ready
//#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/lib/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "flash_ctrl_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static_assert(kBootDataPage0Base == TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR +
                                        FLASH_CTRL_PARAM_BYTES_PER_BANK,
              "Boot data page 0 base address is incorrect.");
static_assert(kBootDataPage1Base == TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR +
                                        FLASH_CTRL_PARAM_BYTES_PER_BANK +
                                        FLASH_CTRL_PARAM_BYTES_PER_PAGE,
              "Boot data page 1 base address is incorrect.");
static_assert(kBootDataEntriesPerPage ==
                  FLASH_CTRL_PARAM_BYTES_PER_PAGE / sizeof(boot_data_t),
              "Number of boot data entries per page is incorrect");
static_assert(sizeof(boot_data_t) % FLASH_CTRL_PARAM_BYTES_PER_WORD == 0,
              "Size of `boot_data_t` must be a multiple of flash word size.");
static_assert(!(FLASH_CTRL_PARAM_BYTES_PER_PAGE &
                (FLASH_CTRL_PARAM_BYTES_PER_PAGE - 1)),
              "Size of a flash page must be a power of two.");
static_assert(!(sizeof(boot_data_t) & (sizeof(boot_data_t) - 1)),
              "Size of `boot_data_t` must be a power of two.");

/**
 * A type that holds `kBootDataNumWords` words.
 */
typedef struct boot_data_buffer {
  uint32_t data[kBootDataNumWords];
} boot_data_buffer_t;

/**
 * Computes the SHA-256 digest of a boot data entry.
 *
 * The region covered by this digest starts immediately after the `identifier`
 * field and ends at the end of the entry.
 *
 * @param boot_data A boot data entry.
 * @param[out] digest Digest of the boot data entry.
 * @return The result of the operation.
 */
static rom_error_t boot_data_digest_compute(const void *boot_data,
                                            hmac_digest_t *digest) {
  enum {
    kDigestRegionOffset = sizeof((boot_data_t){0}.digest),
    kDigestRegionSize = sizeof(boot_data_t) - kDigestRegionOffset,
  };
  static_assert(offsetof(boot_data_t, digest) == 0,
                "`digest` must be the first field of `boot_data_t`.");

  hmac_sha256_init();
  RETURN_IF_ERROR(hmac_sha256_update(
      (const char *)boot_data + kDigestRegionOffset, kDigestRegionSize));
  RETURN_IF_ERROR(hmac_sha256_final(digest));
  return kErrorOk;
}

/**
 * Checks whether the digest of a boot data entry is valid.
 *
 * @param boot_data A buffer that holds a boot data entry.
 * @param[out] is_valid Whether the digest of the entry is valid.
 * @return The result of the operation.
 */
static rom_error_t boot_data_digest_is_valid(
    const boot_data_buffer_t *boot_data, hardened_bool_t *is_valid) {
  static_assert(offsetof(boot_data_t, digest) == 0,
                "`digest` must be the first field of `boot_data_t`.");

  *is_valid = kHardenedBoolFalse;
  hmac_digest_t act_digest;
  RETURN_IF_ERROR(boot_data_digest_compute(boot_data, &act_digest));
  if (memcmp(&act_digest, boot_data, sizeof(act_digest)) == 0) {
    *is_valid = kHardenedBoolTrue;
  }
  return kErrorOk;
}

/**
 * Checks whether a boot data entry is empty.
 *
 * @param boot_data A buffer that holds a boot data entry.
 * @return Whether the entry is empty.
 */
static hardened_bool_t boot_data_is_empty(const boot_data_buffer_t *boot_data) {
  for (size_t i = 0; i < kBootDataNumWords; ++i) {
    if (boot_data->data[i] != kBootDataEmptyWordValue) {
      return kHardenedBoolFalse;
    }
  }
  return kHardenedBoolTrue;
}

/**
 * Returns the address (in bytes) of a boot data entry.
 *
 * @param page_base Page base address in bytes.
 * @param index Index of the entry to read in the given page.
 * @return Address of the entry in bytes.
 */
static uint32_t boot_data_entry_address_get(uint32_t page_base, size_t index) {
  return page_base + index * sizeof(boot_data_t);
}

/**
 * Reads the identifier field of the boot data entry at the given page and
 * index.
 *
 * @param page_base Page base address in bytes.
 * @param index Index of the entry to read in the given page.
 * @param[out] identifier Identifier field of the entry.
 * @return The result of the operation.
 */
static rom_error_t boot_data_identifier_read(uint32_t page_base, size_t index,
                                             uint32_t *identifier) {
  static_assert(offsetof(boot_data_t, identifier) % sizeof(uint32_t) == 0,
                "`identifier` must be word aligned.");

  const uint32_t addr = boot_data_entry_address_get(page_base, index) +
                        offsetof(boot_data_t, identifier);
  // TODO(#8777): Update error handling after switching to silicon_creator
  // driver.
  if (flash_read(addr, kInfoPartition, 1, identifier) != 0) {
    return kErrorBootDataFlash;
  }
  return kErrorOk;
}

/**
 * Reads the boot data entry at the given page and index.
 *
 * @param page_base Page base address in bytes.
 * @param index Index of the entry to read in the given page.
 * @param[out] boot_data A buffer that will hold the entry.
 * @return The result of the operation.
 */
static rom_error_t boot_data_entry_read(uint32_t page_base, size_t index,
                                        boot_data_buffer_t *boot_data) {
  const uint32_t addr = boot_data_entry_address_get(page_base, index);
  // TODO(#8777): Update error handling after switching to silicon_creator
  // driver.
  if (flash_read(addr, kInfoPartition, kBootDataNumWords, boot_data->data) !=
      0) {
    return kErrorBootDataFlash;
  }
  return kErrorOk;
}

/**
 * A struct that stores some information about the first empty and last valid
 * entries in a flash info page.
 */
typedef struct boot_data_page_info {
  /**
   * Base address of the info page.
   */
  uint32_t base_addr;
  /**
   * Whether this page has an empty entry.
   */
  hardened_bool_t has_empty_entry;
  /**
   * Index of the first empty entry.
   */
  size_t first_empty_index;
  /**
   * Whether this page has a valid boot data entry.
   */
  hardened_bool_t has_valid_entry;
  /**
   * Index of the last valid entry in the page.
   */
  size_t last_valid_index;
  /**
   * Last valid entry in the page.
   */
  boot_data_t last_valid_entry;
} boot_data_page_info_t;

/**
 * Populates a page info struct for the given page.
 *
 * This function performs a forward search to find the first empty boot data
 * entry followed by a backward search to find the last valid boot data entry.
 *
 * @param page_base Page base address in bytes.
 * @param[out] page_info Page info struct for the given page.
 * @return The result of the operation.
 */
static rom_error_t boot_data_page_info_get(uint32_t page_base,
                                           boot_data_page_info_t *page_info) {
  uint32_t identifiers[kBootDataEntriesPerPage];
  boot_data_buffer_t buf;

  page_info->base_addr = page_base;
  page_info->has_empty_entry = kHardenedBoolFalse;
  page_info->has_valid_entry = kHardenedBoolFalse;

  // Perform a forward search to find the first empty entry.
  for (size_t i = 0; i < kBootDataEntriesPerPage; ++i) {
    // Read and cache the identifier to quickly determine if an entry can be
    // empty or valid.
    RETURN_IF_ERROR(boot_data_identifier_read(page_base, i, &identifiers[i]));
    // Check all words of this entry only if it can be empty.
    if (identifiers[i] == kBootDataEmptyWordValue) {
      RETURN_IF_ERROR(boot_data_entry_read(page_base, i, &buf));
      if (boot_data_is_empty(&buf) == kHardenedBoolTrue) {
        page_info->first_empty_index = i;
        page_info->has_empty_entry = kHardenedBoolTrue;
        break;
      }
    }
  }

  // Perform a backward search to find the last valid entry.
  size_t start_index = (page_info->has_empty_entry == kHardenedBoolTrue)
                           ? page_info->first_empty_index - 1
                           : kBootDataEntriesPerPage - 1;
  for (size_t i = start_index; i < kBootDataEntriesPerPage; --i) {
    // Check the digest only if this entry can be valid.
    if (identifiers[i] == kBootDataIdentifier) {
      hardened_bool_t is_valid;
      RETURN_IF_ERROR(boot_data_entry_read(page_base, i, &buf));
      RETURN_IF_ERROR(boot_data_digest_is_valid(&buf, &is_valid));
      if (is_valid == kHardenedBoolTrue) {
        memcpy(&page_info->last_valid_entry, &buf, sizeof(buf));
        page_info->last_valid_index = i;
        page_info->has_valid_entry = kHardenedBoolTrue;
        break;
      }
    }
  }

  return kErrorOk;
}

/**
 * Finds the active info page and returns its page info struct.
 *
 * The active info page is the one that has the newest valid boot data entry,
 * i.e. the entry with the greatest counter value.
 *
 * @param[out] page_info Page info struct of the active info page.
 * @return The result of the operation.
 */
static rom_error_t boot_data_active_page_find(
    boot_data_page_info_t *page_info) {
  boot_data_page_info_t page_infos[2];
  RETURN_IF_ERROR(boot_data_page_info_get(kBootDataPage0Base, &page_infos[0]));
  RETURN_IF_ERROR(boot_data_page_info_get(kBootDataPage1Base, &page_infos[1]));

  if (page_infos[0].has_valid_entry == kHardenedBoolTrue &&
      page_infos[1].has_valid_entry == kHardenedBoolTrue) {
    if (page_infos[0].last_valid_entry.counter >
        page_infos[1].last_valid_entry.counter) {
      *page_info = page_infos[0];
      return kErrorOk;
    } else if (page_infos[1].last_valid_entry.counter >
               page_infos[0].last_valid_entry.counter) {
      *page_info = page_infos[1];
      return kErrorOk;
    } else {
      return kErrorBootDataNotFound;
    }
  } else if (page_infos[0].has_valid_entry == kHardenedBoolTrue) {
    *page_info = page_infos[0];
    return kErrorOk;
  } else if (page_infos[1].has_valid_entry == kHardenedBoolTrue) {
    *page_info = page_infos[1];
    return kErrorOk;
  }
  return kErrorBootDataNotFound;
}

/**
 * Default boot data to use if the device is in a non-prod state and there is
 * no valid boot data entry in the flash info pages.
 */
boot_data_t kBootDataDefault = (boot_data_t){
    .digest = {{0xadeb2cd1, 0x9aacb381, 0x45610eeb, 0x129e5fe4, 0x5b56c4ee,
                0x438c2b8c, 0x94d04119, 0x7895f206}},
    .identifier = kBootDataIdentifier,
    // Note: This starts from 5 to have a slightly less trivial value in case we
    // need to distinguish the default entry.
    .counter = 5,
    .min_security_version_rom_ext = 0,
};

/**
 * Returns the default boot data.
 *
 * Default boot data can be used only in TEST_UNLOCKED, DEV, and RMA life cycle
 * states.
 *
 * @param lc_state Life cycle state of the device.
 * @param[out] boot_data Default boot data.
 * @return The result of the operation.
 */
static rom_error_t boot_data_default_get(lifecycle_state_t lc_state,
                                         boot_data_t *boot_data) {
  // TODO(#8778): Default boot data.
  switch (lc_state) {
    case kLcStateTestUnlocked0:
    case kLcStateTestUnlocked1:
    case kLcStateTestUnlocked2:
    case kLcStateTestUnlocked3:
    case kLcStateTestUnlocked4:
    case kLcStateTestUnlocked5:
    case kLcStateTestUnlocked6:
    case kLcStateTestUnlocked7:
    case kLcStateDev:
    case kLcStateRma:
      *boot_data = kBootDataDefault;
      return kErrorOk;
    default:
      return kErrorBootDataNotFound;
  }
}

rom_error_t boot_data_read(lifecycle_state_t lc_state, boot_data_t *boot_data) {
  boot_data_page_info_t active_page;
  rom_error_t error = boot_data_active_page_find(&active_page);
  switch (error) {
    case kErrorOk:
      *boot_data = active_page.last_valid_entry;
      return kErrorOk;
    case kErrorBootDataNotFound:
      // TODO(#8779): Recovery paths for failures in prod life cycle states?
      RETURN_IF_ERROR(boot_data_default_get(lc_state, boot_data));
      return kErrorOk;
    default:
      return error;
  }
}
