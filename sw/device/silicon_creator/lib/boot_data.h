// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_DATA_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_DATA_H_

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Boot data stored in the flash info partition.
 */
typedef struct boot_data {
  /**
   * SHA-256 digest of boot data.
   *
   * The region covered by this digest starts immediately after this field and
   * ends at the end of the entry.
   */
  hmac_digest_t digest;
  /**
   * Invalidation field.
   *
   * This field is used to invalidate the previous entry after writing a new
   * entry. When writing a new entry, the value of this field is assumed to be
   * `kBootDataValidEntry`, which matches the value of unwritten flash words,
   * but it is skipped so that the entry can be invalidated at a later time. An
   * entry can be invalidated by writing `kBootDataInvalidEntry` to this field
   * resulting in a digest mismatch.
   */
  uint64_t is_valid;
  /**
   * Boot data identifier.
   */
  uint32_t identifier;
  /**
   * Boot data format version.
   *
   * This field must be set to the latest version for new entries but is not
   * enforced during reads for forward compatibility in ROM and backward
   * compatibility in ROM_EXT.
   */
  uint32_t version;
  /**
   * Counter.
   *
   * This is a monotonically increasing counter that is used to determine the
   * newest entry across both boot data pages.
   */
  uint32_t counter;
  /**
   * Minimum required security version for ROM_EXT.
   */
  uint32_t min_security_version_rom_ext;
  /**
   * Minimum required security version for BL0.
   */
  uint32_t min_security_version_bl0;
  /**
   * The BL0 slot that is prioritized during boot.
   */
  uint32_t primary_bl0_slot;
  /**
   * Padding for future enhancements and to make the size of `boot_data_t` a
   * power of two.
   */
  uint32_t padding[16];
} boot_data_t;

OT_ASSERT_MEMBER_OFFSET(boot_data_t, digest, 0);
OT_ASSERT_MEMBER_OFFSET(boot_data_t, is_valid, 32);
OT_ASSERT_MEMBER_OFFSET(boot_data_t, identifier, 40);
OT_ASSERT_MEMBER_OFFSET(boot_data_t, version, 44);
OT_ASSERT_MEMBER_OFFSET(boot_data_t, counter, 48);
OT_ASSERT_MEMBER_OFFSET(boot_data_t, min_security_version_rom_ext, 52);
OT_ASSERT_MEMBER_OFFSET(boot_data_t, min_security_version_bl0, 56);
OT_ASSERT_MEMBER_OFFSET(boot_data_t, primary_bl0_slot, 60);
OT_ASSERT_MEMBER_OFFSET(boot_data_t, padding, 64);
OT_ASSERT_SIZE(boot_data_t, 128);

enum {
  /**
   * Boot data identifier value (ASCII "BODA").
   */
  kBootDataIdentifier = 0x41444f42,
  /**
   * Boot data version 1 value.
   */
  kBootDataVersion1 = 0xd4ce468e,
  /**
   * Boot data version 2 value.
   */
  kBootDataVersion2 = 0xad51e729,
  /**
   * Value of the `is_valid` field for valid entries.
   */
  kBootDataValidEntry = UINT64_MAX,
  /**
   * Value of the `is_valid` field for invalidated entries.
   *
   * This value is used to invalidate the previous entry after writing a new
   * entry.
   */
  kBootDataInvalidEntry = 0,
  /**
   * Value of the counter field of the default boot data entry.
   *
   * This starts from 5 to have a slightly less trivial value in case we need to
   * distinguish the default entry.
   */
  kBootDataDefaultCounterVal = 5,
  /**
   * Size of `boot_data_t` in words.
   */
  kBootDataNumWords = sizeof(boot_data_t) / sizeof(uint32_t),
  /**
   * Number of boot data entries per info page.
   *
   * Boot data pages are used as append-only logs where new data is written to
   * the first empty entry of the active page. If all entries of the currently
   * active page are used when `boot_data_write()` is called, the other page
   * will be erased and new data will be written to its first entry, making it
   * the new active page.
   */
  kBootDataEntriesPerPage = 16,
};
static_assert(kBootDataInvalidEntry != kBootDataValidEntry,
              "Invalidation values cannot be equal.");
static_assert(kBootDataValidEntry ==
                  ((uint64_t)kFlashCtrlErasedWord << 32 | kFlashCtrlErasedWord),
              "kBootDataValidEntry words must be kFlashCtrlErasedWord");

/*
 * Encoding generated with
 * $ ./util/design/sparse-fsm-encode.py -d 6 -m 2 -n 32 \
 *     -s 3436204326 --language=c
 *
 * Minimum Hamming distance: 12
 * Maximum Hamming distance: 12
 * Minimum Hamming weight: 15
 * Maximum Hamming weight: 15
 */
enum {
  kBootDataSlotA = 0x9cdc8d50,
  kBootDataSlotB = 0xcd598a4a,
};

/**
 * Reads the boot data stored in the flash info partition.
 *
 * The flash controller must be initialized with proper permissions for the
 * first and second info pages of the second flash bank before calling this
 * function.
 *
 * If there is no valid boot data in the flash info partition, this function
 * returns the default boot data in non-production life cycle states
 * (TEST_UNLOCKED, DEV, RMA).
 *
 * @param lc_state Life cycle state of the device.
 * @param boot_data[out] Boot data.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t boot_data_read(lifecycle_state_t lc_state, boot_data_t *boot_data);

/**
 * Writes the given boot data to the flash info partition.
 *
 * This function updates the `identifier`, `counter`, and `digest` fields of the
 * given `boot_data` before writing it to the flash.
 *
 * @param boot_data[out] Boot data.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t boot_data_write(const boot_data_t *boot_data);

/**
 * Checks whether a boot data entry is valid.
 *
 * This function checks the `identifier` and `digest` fields of the given
 * `boot_data` entry.
 *
 * @param boot_data A buffer that holds a boot data entry.
 * @return Whether the digest of the entry is valid.
 */
OT_WARN_UNUSED_RESULT
rom_error_t boot_data_check(const boot_data_t *boot_data);

/**
 * Populates fields not present in older versions of `boot_data_t`.
 *
 * For older `boot_data_t` entries, some fields may be missing after a call to
 * `boot_data_read()`. This function will populate fields with their default
 * values, the same values that `boot_data_read()` uses when returning default
 * boot data.
 *
 * @param boot_data A buffer the holds a boot data entry.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t boot_data_as_v2(boot_data_t *boot_data);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_DATA_H_
