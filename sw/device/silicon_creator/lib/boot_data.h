// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_DATA_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_DATA_H_

#include "sw/device/lib/base/macros.h"
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
   * Boot data identifier.
   */
  uint32_t identifier;
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
   * Padding to make the size of `boot_data_t` a power of two.
   */
  uint32_t padding[5];
} boot_data_t;

OT_ASSERT_MEMBER_OFFSET(boot_data_t, digest, 0);
OT_ASSERT_MEMBER_OFFSET(boot_data_t, identifier, 32);
OT_ASSERT_MEMBER_OFFSET(boot_data_t, counter, 36);
OT_ASSERT_MEMBER_OFFSET(boot_data_t, min_security_version_rom_ext, 40);
OT_ASSERT_MEMBER_OFFSET(boot_data_t, padding, 44);
OT_ASSERT_SIZE(boot_data_t, 64);

enum {
  /**
   * Boot data identifier value (ASCII "BODA").
   */
  kBootDataIdentifier = 0x41444f42,
  /**
   * Identifier value for invalidated boot data entries.
   *
   * This value is used to invalidate the previous entry after a write.
   */
  kBootDataInvalidatedIdentifier = 0,
  /**
   * Value of a word in flash after erase.
   *
   * This value is used to determine if an entry is empty or not.
   */
  kBootDataEmptyWordValue = UINT32_MAX,
  /**
   * Size of `boot_data_t` in words.
   */
  kBootDataNumWords = sizeof(boot_data_t) / sizeof(uint32_t),
  /**
   * Base address of the first boot data page.
   *
   * The first boot data page is the first info page of the second flash bank.
   */
  kBootDataPage0Base = 0x20080000,
  /**
   * Base address of the second boot data page.
   *
   * The second boot data page is the second info page of the second flash bank.
   */
  kBootDataPage1Base = 0x20080800,
  /**
   * Number of boot data entries per info page.
   *
   * Boot data pages are used as append-only logs where new data is written to
   * the first empty entry of the active page. If all entries of the currently
   * active page are used when `boot_data_write()` is called, the other page
   * will be erased and new data will be written to its first entry, making it
   * the new active page.
   */
  kBootDataEntriesPerPage = 32,
};
static_assert(kBootDataIdentifier != kBootDataEmptyWordValue,
              "Invalid `kBootDataIdentifier` value.");
static_assert(kBootDataIdentifier != kBootDataInvalidatedIdentifier,
              "Invalid `kBootDataIdentifier` value.");

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
rom_error_t boot_data_read(lifecycle_state_t lc_state, boot_data_t *boot_data);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_DATA_H_
