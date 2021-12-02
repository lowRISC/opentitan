// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/boot_data.h"

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "flash_ctrl_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

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
 * Boot data flash info pages.
 */
static const flash_ctrl_info_page_t kPages[2] = {
    kFlashCtrlInfoPageBootData0,
    kFlashCtrlInfoPageBootData1,
};

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
  if (memcmp(&act_digest, boot_data, sizeof(act_digest.digest)) == 0) {
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
 * Reads the identifier field of the boot data entry at the given page and
 * index.
 *
 * @param page A boot data page.
 * @param index Index of the entry to read in the given page.
 * @param[out] identifier Identifier field of the entry.
 * @return The result of the operation.
 */
static rom_error_t boot_data_identifier_read(flash_ctrl_info_page_t page,
                                             size_t index,
                                             uint32_t *identifier) {
  static_assert(offsetof(boot_data_t, identifier) % sizeof(uint32_t) == 0,
                "`identifier` must be word aligned.");
  const uint32_t offset =
      index * sizeof(boot_data_t) + offsetof(boot_data_t, identifier);
  return flash_ctrl_info_read(page, offset, 1, identifier);
}

/**
 * Reads the boot data entry at the given page and index.
 *
 * @param page A boot data page.
 * @param index Index of the entry to read in the given page.
 * @param[out] boot_data A buffer that will hold the entry.
 * @return The result of the operation.
 */
static rom_error_t boot_data_entry_read(flash_ctrl_info_page_t page,
                                        size_t index,
                                        boot_data_buffer_t *boot_data) {
  const uint32_t offset = index * sizeof(boot_data_t);
  return flash_ctrl_info_read(page, offset, kBootDataNumWords, boot_data->data);
}

/**
 * Populates the boot data entry at the given page and index.
 *
 * If `erase` is `kHardenedBoolTrue`, this function erases the given page before
 * writing the new entry. This function also also verifies the newly written
 * entry by reading it back. Reads, writes, and erases (if applicable) must be
 * enabled for the given page before this function is called, see
 * `boot_data_entry_write()`.
 *
 * @param page A boot data page.
 * @param index Index of the entry to write in the given page.
 * @param boot_data Entry to write.
 * @param erase Whether to erase the page before writing the entry.
 * @return The result of the operation.
 */
static rom_error_t boot_data_entry_write_impl(flash_ctrl_info_page_t page,
                                              size_t index,
                                              const boot_data_t *boot_data,
                                              hardened_bool_t erase) {
  boot_data_buffer_t buf;
  memcpy(&buf, boot_data, sizeof(boot_data_t));
  const uint32_t offset = index * sizeof(boot_data_t);
  if (erase == kHardenedBoolTrue) {
    RETURN_IF_ERROR(flash_ctrl_info_erase(page, kFlashCtrlEraseTypePage));
  }
  RETURN_IF_ERROR(
      flash_ctrl_info_write(page, offset, kBootDataNumWords, buf.data));
  RETURN_IF_ERROR(
      flash_ctrl_info_read(page, offset, kBootDataNumWords, buf.data));
  if (memcmp(&buf, boot_data, sizeof(boot_data_t)) != 0) {
    return kErrorBootDataWriteCheck;
  }
  return kErrorOk;
}

/**
 * Handles access permissions and populates the boot data entry at the given
 * page and index.
 *
 * This function wraps the actual implementation to enable and disable reads,
 * writes, and erases (if applicable) for the given page, see
 * `boot_data_page_entry_write_impl()`.
 *
 * @param page A boot data page.
 * @param index Index of the entry to write in the given page.
 * @param boot_data Entry to write.
 * @param erase Whether to erase the page before writing the entry.
 * @return The result of the operation.
 */
static rom_error_t boot_data_entry_write(flash_ctrl_info_page_t page,
                                         size_t index,
                                         const boot_data_t *boot_data,
                                         hardened_bool_t erase) {
  flash_ctrl_info_mp_set(page, (flash_ctrl_mp_t){
                                   .read = kHardenedBoolTrue,
                                   .write = kHardenedBoolTrue,
                                   .erase = erase,
                               });
  rom_error_t error = boot_data_entry_write_impl(page, index, boot_data, erase);
  flash_ctrl_info_mp_set(page, (flash_ctrl_mp_t){
                                   .read = kHardenedBoolFalse,
                                   .write = kHardenedBoolFalse,
                                   .erase = kHardenedBoolFalse,
                               });
  return error;
}

/**
 * Invalidates the boot data entry at the given page and index.
 *
 * This function handles write permissions for the given page and sets the
 * `identifier` field of the given entry to `kBootDataInvalidatedIdentifier`
 * which will cause both the identifier and the digest checks to fail in
 * subsequent reads.
 *
 * This function must be called only after the new entry is successfully
 * written since writes can potentially be interrupted.
 *
 * @param page A boot data page.
 * @param index Index of the entry to invalidate in the given page.
 * @return The result of the operation.
 */
static rom_error_t boot_data_entry_invalidate(flash_ctrl_info_page_t page,
                                              size_t index) {
  static_assert(offsetof(boot_data_t, identifier) % sizeof(uint32_t) == 0,
                "`identifier` must be word aligned.");

  const uint32_t offset =
      index * sizeof(boot_data_t) + offsetof(boot_data_t, identifier);
  const uint32_t val = kBootDataInvalidatedIdentifier;
  flash_ctrl_info_mp_set(page, (flash_ctrl_mp_t){
                                   .read = kHardenedBoolFalse,
                                   .write = kHardenedBoolTrue,
                                   .erase = kHardenedBoolFalse,
                               });
  rom_error_t error = flash_ctrl_info_write(page, offset, 1, &val);
  flash_ctrl_info_mp_set(page, (flash_ctrl_mp_t){
                                   .read = kHardenedBoolFalse,
                                   .write = kHardenedBoolFalse,
                                   .erase = kHardenedBoolFalse,
                               });
  return error;
}

/**
 * A struct that stores some information about the first empty and last valid
 * entries in a flash info page.
 */
typedef struct boot_data_page_info {
  /**
   * Info page.
   */
  flash_ctrl_info_page_t page;
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
 * Reads must be enabled for the given page before this function is called, see
 * `boot_data_page_info_get()`.
 *
 * @param page A boot data page.
 * @param[out] page_info Page info struct for the given page.
 * @return The result of the operation.
 */
static rom_error_t boot_data_page_info_get_impl(
    flash_ctrl_info_page_t page, boot_data_page_info_t *page_info) {
  uint32_t identifiers[kBootDataEntriesPerPage];
  boot_data_buffer_t buf;

  page_info->page = page;
  page_info->has_empty_entry = kHardenedBoolFalse;
  page_info->has_valid_entry = kHardenedBoolFalse;

  // Perform a forward search to find the first empty entry.
  for (size_t i = 0; i < kBootDataEntriesPerPage; ++i) {
    // Read and cache the identifier to quickly determine if an entry can be
    // empty or valid.
    RETURN_IF_ERROR(boot_data_identifier_read(page, i, &identifiers[i]));
    // Check all words of this entry only if it can be empty.
    if (identifiers[i] == kBootDataEmptyWordValue) {
      RETURN_IF_ERROR(boot_data_entry_read(page, i, &buf));
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
      RETURN_IF_ERROR(boot_data_entry_read(page, i, &buf));
      RETURN_IF_ERROR(boot_data_digest_is_valid(&buf, &is_valid));
      if (is_valid == kHardenedBoolTrue) {
        memcpy(&page_info->last_valid_entry, &buf, sizeof(boot_data_t));
        page_info->last_valid_index = i;
        page_info->has_valid_entry = kHardenedBoolTrue;
        break;
      }
    }
  }

  return kErrorOk;
}

/**
 * Handles read permissions and populates a page info struct for the given page.
 *
 * This function wraps the actual implementation to enable and disable reads for
 * the given page, see `boot_data_page_info_get_impl()`.
 *
 * @param page A boot data page.
 * @param[out] page_info Page info struct for the given page.
 * @return The result of the operation.
 */
static rom_error_t boot_data_page_info_get(flash_ctrl_info_page_t page,
                                           boot_data_page_info_t *page_info) {
  flash_ctrl_info_mp_set(page, (flash_ctrl_mp_t){
                                   .read = kHardenedBoolTrue,
                                   .write = kHardenedBoolFalse,
                                   .erase = kHardenedBoolFalse,
                               });
  rom_error_t error = boot_data_page_info_get_impl(page, page_info);
  flash_ctrl_info_mp_set(page, (flash_ctrl_mp_t){
                                   .read = kHardenedBoolFalse,
                                   .write = kHardenedBoolFalse,
                                   .erase = kHardenedBoolFalse,
                               });
  return error;
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
  for (size_t i = 0; i < ARRAYSIZE(kPages); ++i) {
    RETURN_IF_ERROR(boot_data_page_info_get(kPages[i], &page_infos[i]));
  }

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

rom_error_t boot_data_write(const boot_data_t *boot_data) {
  boot_data_t new_entry = *boot_data;
  new_entry.identifier = kBootDataIdentifier;
  boot_data_page_info_t active_page;
  rom_error_t error = boot_data_active_page_find(&active_page);

  if (error == kErrorOk) {
    // Note: Not checking for wraparound since a successful write will
    // invalidate the old entry.
    new_entry.counter = active_page.last_valid_entry.counter + 1;
    RETURN_IF_ERROR(boot_data_digest_compute(&new_entry, &new_entry.digest));
    if (active_page.has_empty_entry == kHardenedBoolTrue) {
      RETURN_IF_ERROR(boot_data_entry_write(active_page.page,
                                            active_page.first_empty_index,
                                            &new_entry, kHardenedBoolFalse));
    } else {
      // Erase the other page and write the new entry there if the active page
      // is full.
      flash_ctrl_info_page_t new_page =
          active_page.page == kPages[0] ? kPages[1] : kPages[0];
      RETURN_IF_ERROR(
          boot_data_entry_write(new_page, 0, &new_entry, kHardenedBoolTrue));
    }
    // Invalidate the previous entry so that there is only one valid entry
    // across both pages.
    RETURN_IF_ERROR(boot_data_entry_invalidate(active_page.page,
                                               active_page.last_valid_index));
  } else if (error == kErrorBootDataNotFound) {
    // Erase the first page and write the entry there if the active page cannot
    // be found, i.e. the storage is not initialized yet.
    new_entry.counter = kBootDataDefault.counter + 1;
    RETURN_IF_ERROR(boot_data_digest_compute(&new_entry, &new_entry.digest));
    RETURN_IF_ERROR(
        boot_data_entry_write(kPages[0], 0, &new_entry, kHardenedBoolTrue));
  } else {
    return error;
  }

  return kErrorOk;
}
