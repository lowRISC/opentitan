// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/boot_data.h"

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "flash_ctrl_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"

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
OT_ASSERT_MEMBER_SIZE(boot_data_t, is_valid, FLASH_CTRL_PARAM_BYTES_PER_WORD);
static_assert(offsetof(boot_data_t, is_valid) %
                      FLASH_CTRL_PARAM_BYTES_PER_WORD ==
                  0,
              "`is_valid` must be flash word aligned.");

enum {
  /**
   * Number of boot data flash info pages.
   */
  kPageCount = 2,
};
/**
 * Boot data flash info pages.
 */
static const flash_ctrl_info_page_t kPages[kPageCount] = {
    kFlashCtrlInfoPageBootData0,
    kFlashCtrlInfoPageBootData1,
};

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
static void boot_data_digest_compute(const void *boot_data,
                                     hmac_digest_t *digest) {
  enum {
    kDigestRegionOffset = sizeof((boot_data_t){0}.digest),
    kDigestRegionSize = sizeof(boot_data_t) - kDigestRegionOffset,
  };
  static_assert(offsetof(boot_data_t, digest) == 0,
                "`digest` must be the first field of `boot_data_t`.");

  hmac_sha256_init();
  hmac_sha256_update((const char *)boot_data + kDigestRegionOffset,
                     kDigestRegionSize);
  hmac_sha256_final(digest);
}

/**
 * Checks whether a boot data entry is empty.
 *
 * @param boot_data A buffer that holds a boot data entry. Must be word aligned.
 * @return Whether the entry is empty.
 */
static hardened_bool_t boot_data_is_empty(const void *boot_data) {
  static_assert(kFlashCtrlErasedWord == UINT32_MAX,
                "kFlashCtrlErasedWord must be UINT32_MAX");
  size_t i = 0, r = kBootDataNumWords - 1;
  hardened_bool_t is_empty = kHardenedBoolTrue;
  uint32_t res = kFlashCtrlErasedWord;
  for (; launder32(i) < kBootDataNumWords && launder32(r) < kBootDataNumWords;
       ++i, --r) {
    res &= read_32(boot_data);
    is_empty &= read_32(boot_data);
    boot_data = (char *)boot_data + sizeof(uint32_t);
  }
  HARDENED_CHECK_EQ(i, kBootDataNumWords);
  HARDENED_CHECK_EQ((uint32_t)r, UINT32_MAX);
  if (launder32(res) == kFlashCtrlErasedWord) {
    HARDENED_CHECK_EQ(res, kFlashCtrlErasedWord);
    return is_empty;
  }
  return kHardenedBoolFalse;
}

/**
 * Returns the `identifier` of the boot data entry at the given page and
 * index after masking it with the words of its `is_valid` field.
 *
 * This function can be used to quickly determine if an entry can be empty or
 * valid. Due to the values chosen for valid and invalid entries,
 * `masked_identifier` will be `kFlashCtrlErasedWord` for entries that can be
 * empty, `kBootDataIdentifier` for entries that are not invalidated, and `0`
 * for invalidated entries.
 *
 * @param page A boot data page.
 * @param index Index of the entry to read in the given page.
 * @param[out] masked_identifier Identifier masked with the words of `is_valid`.
 * @return The result of the operation.
 */
static rom_error_t boot_data_sniff(flash_ctrl_info_page_t page, size_t index,
                                   uint32_t *masked_identifier) {
  static_assert(kBootDataValidEntry == UINT64_MAX,
                "is_valid must be UINT64_MAX for valid entries.");
  static_assert(kBootDataInvalidEntry == 0,
                "is_valid must be 0 for invalid entries.");

  enum {
    kIsValidOffset = offsetof(boot_data_t, is_valid),
    kIdentifierOffset = offsetof(boot_data_t, identifier),
  };
  static_assert(
      kIdentifierOffset - kIsValidOffset == sizeof((boot_data_t){0}.is_valid),
      "is_valid and identifier must be consecutive.");

  *masked_identifier = 0;
  uint32_t buf[3];
  const uint32_t offset = index * sizeof(boot_data_t) + kIsValidOffset;
  HARDENED_RETURN_IF_ERROR(flash_ctrl_info_read(page, offset, 3, buf));
  *masked_identifier = buf[0] & buf[1] & buf[2];
  return kErrorOk;
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
                                        size_t index, boot_data_t *boot_data) {
  const uint32_t offset = index * sizeof(boot_data_t);
  return flash_ctrl_info_read(page, offset, kBootDataNumWords, boot_data);
}

/**
 * Populates the boot data entry at the given page and index.
 *
 * This function writes the new entry in two transactions skipping over the
 * `is_valid` field so that the entry can be invalidated later. If `erase` is
 * `kHardenedBoolTrue`, this function erases the given page before writing the
 * new entry. This function also also verifies the newly written entry by
 * reading it back. Reads, writes, and erases (if applicable) must be enabled
 * for the given page before this function is called, see
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
  // This function assumes the following layout for the first three fields.
  OT_ASSERT_MEMBER_OFFSET(boot_data_t, digest, 0);
  OT_ASSERT_MEMBER_OFFSET(boot_data_t, is_valid, 32);
  OT_ASSERT_MEMBER_OFFSET(boot_data_t, identifier, 40);

  if (erase == kHardenedBoolTrue) {
    RETURN_IF_ERROR(flash_ctrl_info_erase(page, kFlashCtrlEraseTypePage));
  }

  // Write digest
  const uint32_t offset = index * sizeof(boot_data_t);
  RETURN_IF_ERROR(
      flash_ctrl_info_write(page, offset, kHmacDigestNumWords, boot_data));
  // Write the rest of the entry, skipping over `is_valid`.
  enum {
    kSecondWriteOffsetBytes = offsetof(boot_data_t, identifier),
    kSecondWriteOffsetWords = kSecondWriteOffsetBytes / sizeof(uint32_t),
    kSecondWriteNumWords = kBootDataNumWords - kSecondWriteOffsetWords,
  };
  RETURN_IF_ERROR(flash_ctrl_info_write(
      page, offset + kSecondWriteOffsetBytes, kSecondWriteNumWords,
      (const char *)boot_data + kSecondWriteOffsetBytes));

  // Check.
  boot_data_t written;
  RETURN_IF_ERROR(
      flash_ctrl_info_read(page, offset, kBootDataNumWords, &written));
  if (memcmp(&written, boot_data, sizeof(boot_data_t)) != 0) {
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
  flash_ctrl_info_perms_set(
      page, (flash_ctrl_perms_t){
                .read = kMultiBitBool4True,
                .write = kMultiBitBool4True,
                .erase = erase == kHardenedBoolTrue ? kMultiBitBool4True
                                                    : kMultiBitBool4False,
            });
  rom_error_t error = boot_data_entry_write_impl(page, index, boot_data, erase);
  flash_ctrl_info_perms_set(page, (flash_ctrl_perms_t){
                                      .read = kMultiBitBool4False,
                                      .write = kMultiBitBool4False,
                                      .erase = kMultiBitBool4False,
                                  });
  SEC_MMIO_WRITE_INCREMENT(2 * kFlashCtrlSecMmioInfoPermsSet);
  return error;
}

/**
 * Invalidates the boot data entry at the given page and index.
 *
 * This function handles write permissions for the given page and sets the
 * `is_valid` field of the given entry to `kBootDataInvalidEntry` which will
 * cause the digest checks to fail in subsequent reads.
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
  // Assertions for the assumptions below.
  OT_ASSERT_MEMBER_SIZE(boot_data_t, is_valid, 8);
  static_assert(kBootDataInvalidEntry == 0,
                "Unexpected kBootDataInvalidEntry value.");

  const uint32_t offset =
      index * sizeof(boot_data_t) + offsetof(boot_data_t, is_valid);
  const uint32_t val[2] = {0, 0};
  flash_ctrl_info_perms_set(page, (flash_ctrl_perms_t){
                                      .read = kMultiBitBool4False,
                                      .write = kMultiBitBool4True,
                                      .erase = kMultiBitBool4False,
                                  });
  rom_error_t error = flash_ctrl_info_write(page, offset, 2, val);
  flash_ctrl_info_perms_set(page, (flash_ctrl_perms_t){
                                      .read = kMultiBitBool4False,
                                      .write = kMultiBitBool4False,
                                      .erase = kMultiBitBool4False,
                                  });
  SEC_MMIO_WRITE_INCREMENT(2 * kFlashCtrlSecMmioInfoPermsSet);
  return error;
}

/**
 * A struct that stores some information about the first empty and last valid
 * entries in the active flash info page.
 */
typedef struct active_page_info {
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
} active_page_info_t;

/**
 * Updates the given active page info struct and last valid boot data entry
 * using the given page.
 *
 * This function performs a forward search to find the first empty boot data
 * entry followed by a backward search to find the last valid boot data entry.
 * If the page has an entry that is newer than the one passed in, this function
 * updates `page_info` and `boot_data`. Reads must be enabled for the given page
 * before this function is called, see `boot_data_page_info_get()`.
 *
 * @param page A boot data page.
 * @param[in,out] page_info Active page info struct. Updated if the given page
 * has a newer entry.
 * @param[in,out] boot_data Last valid boot data entry found so far. Updated if
 * the given page has a newer entry.
 * @return The result of the operation.
 */
static rom_error_t boot_data_page_info_update_impl(
    flash_ctrl_info_page_t page, active_page_info_t *page_info,
    boot_data_t *boot_data) {
  uint32_t sniff_results[kBootDataEntriesPerPage];

  boot_data_t buf;

  // Perform a forward search to find the first empty entry.
  hardened_bool_t has_empty_entry = kHardenedBoolFalse;
  size_t i = 0, r = kBootDataEntriesPerPage - 1;
  for (; launder32(i) < kBootDataEntriesPerPage &&
         launder32(r) < kBootDataEntriesPerPage;
       ++i, --r) {
    // Read and cache the identifier to quickly determine if an entry can be
    // empty or valid.
    HARDENED_RETURN_IF_ERROR(boot_data_sniff(page, i, &sniff_results[i]));
    // Check all words of this entry only if it can be empty.
    if (sniff_results[i] == kFlashCtrlErasedWord) {
      HARDENED_RETURN_IF_ERROR(boot_data_entry_read(page, i, &buf));
      has_empty_entry = boot_data_is_empty(&buf);
      if (launder32(has_empty_entry) == kHardenedBoolTrue) {
        HARDENED_CHECK_EQ(has_empty_entry, kHardenedBoolTrue);
        break;
      }
      HARDENED_CHECK_EQ(has_empty_entry, kHardenedBoolFalse);
    }
  }
  // At the end of this loop, `i` is the index of the first empty entry if any
  // and `kBootDataEntriesPerPage` otherwise.
  HARDENED_CHECK_LE(i, kBootDataEntriesPerPage);
  size_t first_empty_index = i;
  HARDENED_CHECK_EQ(i + r, kBootDataEntriesPerPage - 1);

  // Perform a backward search to find the last valid entry.
  hardened_bool_t has_valid_entry = kHardenedBoolFalse;
  for (--i, ++r; launder32(i) < kBootDataEntriesPerPage &&
                 launder32(r) < kBootDataEntriesPerPage;
       --i, ++r) {
    // Check the digest only if this entry can be valid.
    if (sniff_results[i] == kBootDataIdentifier) {
      HARDENED_RETURN_IF_ERROR(boot_data_entry_read(page, i, &buf));
      rom_error_t is_valid = boot_data_check(&buf);
      if (launder32(is_valid) == kErrorOk) {
        HARDENED_CHECK_EQ(is_valid, kErrorOk);
        static_assert(kErrorOk == (rom_error_t)kHardenedBoolTrue,
                      "kErrorOk must be equal to kHardenedBoolTrue");
        has_valid_entry = (hardened_bool_t)is_valid;
        break;
      }
      HARDENED_CHECK_EQ(is_valid, kErrorBootDataInvalid);
    }
  }
  // At the end of this loop, `i` is the index of the last valid entry if any
  // and `UINT32_MAX`, otherwise. `r` must be less than or equal to
  // `first_empty_index`.
  HARDENED_CHECK_EQ(i + r, kBootDataEntriesPerPage - 1);

  if (launder32(has_valid_entry) == kHardenedBoolTrue) {
    HARDENED_CHECK_EQ(has_valid_entry, kHardenedBoolTrue);
    if (launder32(page_info->has_valid_entry) == kHardenedBoolFalse) {
      // Update `page_info` and `boot_data` since this is the first valid entry.
      HARDENED_CHECK_EQ(page_info->has_valid_entry, kHardenedBoolFalse);
      *page_info = (active_page_info_t){
          .page = page,
          .has_empty_entry = has_empty_entry,
          .first_empty_index = first_empty_index,
          .has_valid_entry = has_valid_entry,
          .last_valid_index = i,
      };
      *boot_data = buf;
    } else if (launder32(page_info->has_valid_entry) == kHardenedBoolTrue &&
               launder32(buf.counter) > boot_data->counter) {
      // Update `page_info` and `boot_data` since this entry is newer.
      HARDENED_CHECK_EQ(page_info->has_valid_entry, kHardenedBoolTrue);
      HARDENED_CHECK_GT(buf.counter, boot_data->counter);
      *page_info = (active_page_info_t){
          .page = page,
          .has_empty_entry = has_empty_entry,
          .first_empty_index = first_empty_index,
          .has_valid_entry = has_valid_entry,
          .last_valid_index = i,
      };
      *boot_data = buf;
    } else {
      HARDENED_CHECK_EQ(page_info->has_valid_entry, kHardenedBoolTrue);
      // Counters cannot be equal if we have two valid entries since they are
      // incremented at each write.
      HARDENED_CHECK_LT(buf.counter, boot_data->counter);
    }
  }

  return kErrorOk;
}

/**
 * Handles read permissions and updates the active page info struct and last
 * valid boot data entry using the given page.
 *
 * This function wraps the actual implementation to enable and disable reads for
 * the given page, see `boot_data_page_info_get_impl()`.
 *
 * @param page A boot data page.
 * @param[in,out] page_info Active page info struct. Updated if the given page
 * has a newer entry.
 * @param[in,out] boot_data Last valid boot data entry found so far. Updated if
 * the given page has a newer entry.
 * @return The result of the operation.
 */
static rom_error_t boot_data_page_info_update(flash_ctrl_info_page_t page,
                                              active_page_info_t *page_info,
                                              boot_data_t *boot_data) {
  flash_ctrl_info_perms_set(page, (flash_ctrl_perms_t){
                                      .read = kMultiBitBool4True,
                                      .write = kMultiBitBool4False,
                                      .erase = kMultiBitBool4False,
                                  });
  rom_error_t error =
      boot_data_page_info_update_impl(page, page_info, boot_data);
  flash_ctrl_info_perms_set(page, (flash_ctrl_perms_t){
                                      .read = kMultiBitBool4False,
                                      .write = kMultiBitBool4False,
                                      .erase = kMultiBitBool4False,
                                  });
  SEC_MMIO_WRITE_INCREMENT(2 * kFlashCtrlSecMmioInfoPermsSet);
  return error;
}

/**
 * Finds the active info page and returns its page info struct and last boot
 * data entry.
 *
 * The active info page is the one that has the newest valid boot data entry,
 * i.e. the entry with the greatest counter value.
 *
 * @param[out] page_info Page info struct of the active info page.
 * @param[out] boot_data Last valid boot data entry.
 * @return The result of the operation.
 */
static rom_error_t boot_data_active_page_find(active_page_info_t *page_info,
                                              boot_data_t *boot_data) {
  *page_info = (active_page_info_t){
      .page = (flash_ctrl_info_page_t)0,
      .has_empty_entry = kHardenedBoolFalse,
      .first_empty_index = kBootDataEntriesPerPage,
      .has_valid_entry = kHardenedBoolFalse,
      .last_valid_index = kBootDataEntriesPerPage,
  };

  static_assert(kPageCount == 2,
                "Number of pages changed, unrolled loop must be updated");
  HARDENED_RETURN_IF_ERROR(
      boot_data_page_info_update(kPages[0], page_info, boot_data));
  HARDENED_RETURN_IF_ERROR(
      boot_data_page_info_update(kPages[1], page_info, boot_data));

  return kErrorOk;
}

/**
 * Returns the default boot data.
 *
 * Default boot data can be used only in TEST_UNLOCKED, DEV, and RMA life cycle
 * states unless explicitly allowed by setting the
 * `CREATOR_SW_CFG_DEFAULT_BOOT_DATA_IN_PROD_EN` OTP item to
 * `kHardenedBoolTrue`.
 *
 * @param lc_state Life cycle state of the device.
 * @param[out] boot_data Default boot data.
 * @return The result of the operation.
 */
static rom_error_t boot_data_default_get(lifecycle_state_t lc_state,
                                         boot_data_t *boot_data) {
  uint32_t allowed_in_prod = otp_read32(
      OTP_CTRL_PARAM_CREATOR_SW_CFG_DEFAULT_BOOT_DATA_IN_PROD_EN_OFFSET);
  rom_error_t res = lc_state ^ launder32(kErrorBootDataNotFound);
  barrier32(res);
  switch (launder32(lc_state)) {
    case kLcStateTest:
      HARDENED_CHECK_EQ(lc_state, kLcStateTest);
      res ^= kLcStateTest ^ kErrorBootDataNotFound ^ kErrorOk;
      break;
    case kLcStateDev:
      HARDENED_CHECK_EQ(lc_state, kLcStateDev);
      res ^= kLcStateDev ^ kErrorBootDataNotFound ^ kErrorOk;
      break;
    case kLcStateProd:
      HARDENED_CHECK_EQ(lc_state, kLcStateProd);
      res ^= kLcStateProd;
      if (launder32(allowed_in_prod) == kHardenedBoolTrue) {
        HARDENED_CHECK_EQ(allowed_in_prod, kHardenedBoolTrue);
        res ^= kErrorBootDataNotFound ^ kErrorOk;
      }
      break;
    case kLcStateProdEnd:
      HARDENED_CHECK_EQ(lc_state, kLcStateProdEnd);
      res ^= kLcStateProdEnd;
      if (launder32(allowed_in_prod) == kHardenedBoolTrue) {
        HARDENED_CHECK_EQ(allowed_in_prod, kHardenedBoolTrue);
        res ^= kErrorBootDataNotFound ^ kErrorOk;
      }
      break;
    case kLcStateRma:
      HARDENED_CHECK_EQ(lc_state, kLcStateRma);
      res ^= kLcStateRma ^ kErrorBootDataNotFound ^ kErrorOk;
      break;
    default:
      HARDENED_TRAP();
  }

  HARDENED_RETURN_IF_ERROR(res);

  boot_data->is_valid = kBootDataValidEntry;
  boot_data->identifier = kBootDataIdentifier;
  boot_data->counter = kBootDataDefaultCounterVal;
  boot_data->min_security_version_rom_ext =
      otp_read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_MIN_SEC_VER_ROM_EXT_OFFSET);
  boot_data->min_security_version_bl0 =
      otp_read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_MIN_SEC_VER_BL0_OFFSET);
  // We cannot use a constant digest since some fields are read from the OTP
  // and we check the digest of the cached boot data entry in rom.c
  boot_data_digest_compute(boot_data, &boot_data->digest);

  return res;
}

rom_error_t boot_data_read(lifecycle_state_t lc_state, boot_data_t *boot_data) {
  active_page_info_t active_page;
  HARDENED_RETURN_IF_ERROR(boot_data_active_page_find(&active_page, boot_data));
  switch (launder32(active_page.has_valid_entry)) {
    case kHardenedBoolTrue:
      HARDENED_CHECK_EQ(active_page.has_valid_entry, kHardenedBoolTrue);
      return kErrorOk;
    case kHardenedBoolFalse:
      HARDENED_CHECK_EQ(active_page.has_valid_entry, kHardenedBoolFalse);
      return boot_data_default_get(lc_state, boot_data);
    default:
      HARDENED_TRAP();
      OT_UNREACHABLE();
  }
}

rom_error_t boot_data_write(const boot_data_t *boot_data) {
  boot_data_t new_entry = *boot_data;
  new_entry.is_valid = kBootDataValidEntry;
  new_entry.identifier = kBootDataIdentifier;
  active_page_info_t active_page;
  boot_data_t last_entry;
  RETURN_IF_ERROR(boot_data_active_page_find(&active_page, &last_entry));

  if (active_page.has_valid_entry == kHardenedBoolTrue) {
    // Note: Not checking for wraparound since a successful write will
    // invalidate the old entry.
    new_entry.counter = last_entry.counter + 1;
    boot_data_digest_compute(&new_entry, &new_entry.digest);
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
  } else {
    // Erase the first page and write the entry there if the active page cannot
    // be found, i.e. the storage is not initialized yet.
    new_entry.counter = kBootDataDefaultCounterVal + 1;
    boot_data_digest_compute(&new_entry, &new_entry.digest);
    RETURN_IF_ERROR(
        boot_data_entry_write(kPages[0], 0, &new_entry, kHardenedBoolTrue));
  }

  return kErrorOk;
}

/**
 * Shares for producing the `error` value in `boot_data_check()`. First 8
 * shares are generated using the `sparse-fsm-encode` script while the last
 * share is `kErrorOk ^ kBootDataInvalid ^ kBootDataIdentifier ^
 * kCheckShares[0] ^ ... ^ kCheckShares[7]` so that xor'ing all shares with
 * the initial value of `error`, i.e. `kErrorBootDataInvalid`, and
 * `kBootDataIdentifier` produces `kErrorOk`.
 *
 * Encoding generated with
 * $ ./util/design/sparse-fsm-encode.py -d 6 -m 8 -n 32 \
 *     -s 49105412 --language=c
 *
 * Minimum Hamming distance: 12
 * Maximum Hamming distance: 23
 * Minimum Hamming weight: 13
 * Maximum Hamming weight: 20
 */
static const uint32_t kCheckShares[kHmacDigestNumWords + 1] = {
    0xe021e1a9, 0xf81e8365, 0xbf8322db, 0xc7a37080, 0x271a933f,
    0xdd8ce33f, 0x7585d574, 0x951777af, 0x381dee3a,
};

/**
 * Checks whether the digest of a boot data entry is valid.
 *
 * @param boot_data A buffer that holds a boot data entry.
 * @return Whether the digest of the entry is valid.
 */
rom_error_t boot_data_check(const boot_data_t *boot_data) {
  static_assert(offsetof(boot_data_t, digest) == 0,
                "`digest` must be the first field of `boot_data_t`.");

  rom_error_t error = kErrorBootDataInvalid;
  hmac_digest_t act_digest;
  boot_data_digest_compute(boot_data, &act_digest);

  size_t i = 0;
  for (; launder32(i) < kHmacDigestNumWords; ++i) {
    error ^=
        boot_data->digest.digest[i] ^ act_digest.digest[i] ^ kCheckShares[i];
  }
  HARDENED_CHECK_EQ(i, kHmacDigestNumWords);
  error ^= boot_data->identifier ^ kCheckShares[kHmacDigestNumWords];
  if (launder32(error) == kErrorOk) {
    HARDENED_CHECK_EQ(error, kErrorOk);
    return error;
  }

  return kErrorBootDataInvalid;
}
