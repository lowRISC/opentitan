// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"

#include "flash_ctrl_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"

OTTF_DEFINE_TEST_CONFIG();

/**
 * Boot data flash info pages.
 */
static const flash_ctrl_info_page_t kPages[2] = {
    kFlashCtrlInfoPageBootData0,
    kFlashCtrlInfoPageBootData1,
};

/**
 * Boot data entry used in tests.
 */
boot_data_t kTestBootData = (boot_data_t){
    .digest = {{0x00f0046c, 0x34e7a3d5, 0x93b15c2e, 0x77cbd502, 0x3d0530f6,
                0xa58d38b2, 0x60693f97, 0x67e132d9}},
    .identifier = kBootDataIdentifier,
    .is_valid = kBootDataValidEntry,
    // `kBootDataDefaultCounterVal` + 1 for consistency.
    .counter = kBootDataDefaultCounterVal + 1,
    .min_security_version_rom_ext = 0,
};

/**
 * Sets read, write, and erase permissions for boot data pages.
 *
 * This function is intended for backdoor access during tests, e.g. to set the
 * contents of a page before a read test or check the contents after a write
 * test.
 *
 * @param enable New read, write, and erase permissions.
 */
static void boot_data_pages_mp_set(hardened_bool_t perm) {
  multi_bit_bool_t mubi_perm =
      perm == kHardenedBoolTrue ? kMultiBitBool4True : kMultiBitBool4False;
  for (size_t i = 0; i < ARRAYSIZE(kPages); ++i) {
    flash_ctrl_info_perms_set(kPages[i], (flash_ctrl_perms_t){
                                             .read = mubi_perm,
                                             .write = mubi_perm,
                                             .erase = mubi_perm,
                                         });
  }
}

/**
 * Erases boot data info pages.
 */
static void erase_boot_data_pages(void) {
  boot_data_pages_mp_set(kHardenedBoolTrue);
  for (size_t i = 0; i < ARRAYSIZE(kPages); ++i) {
    CHECK(flash_ctrl_info_erase(kPages[i], kFlashCtrlEraseTypePage) == kErrorOk,
          "Flash page erase failed.");
  }
  boot_data_pages_mp_set(kHardenedBoolFalse);
}

/**
 * Writes a boot data entry at the given page and index.
 *
 * This function also checks that the entry was written correctly by reading it
 * back from the flash.
 *
 * @param page Flash info page.
 * @param index Index of the entry to write in the given page.
 * @param boot_data A boot data entry.
 */
static void write_boot_data(flash_ctrl_info_page_t page, size_t index,
                            const boot_data_t *boot_data) {
  const uint32_t offset = index * sizeof(boot_data_t);
  uint32_t buf[kBootDataNumWords];
  memcpy(buf, boot_data, sizeof(boot_data_t));
  boot_data_pages_mp_set(kHardenedBoolTrue);
  CHECK(flash_ctrl_info_write(page, offset, kBootDataNumWords, buf) == kErrorOk,
        "Flash write failed.");
  CHECK(flash_ctrl_info_read(page, offset, kBootDataNumWords, buf) == kErrorOk,
        "Flash read failed.");
  boot_data_pages_mp_set(kHardenedBoolFalse);
  CHECK(memcmp(buf, boot_data, sizeof(boot_data_t)) == 0,
        "Flash write failed.");
}

/**
 * Reads the boot data entry at the given page and index.
 *
 * @param page Flash info page.
 * @param index Index of the entry to read in the given page.
 * @param boot_data A boot data entry.
 */
static void read_boot_data(flash_ctrl_info_page_t page, size_t index,
                           boot_data_t *boot_data) {
  const uint32_t offset = index * sizeof(boot_data_t);
  uint32_t buf[kBootDataNumWords];
  boot_data_pages_mp_set(kHardenedBoolTrue);
  CHECK(flash_ctrl_info_read(page, offset, kBootDataNumWords, buf) == kErrorOk,
        "Flash read failed.");
  boot_data_pages_mp_set(kHardenedBoolFalse);
  memcpy(boot_data, buf, sizeof(boot_data_t));
}

/**
 * Writes the given number of invalidated boot data entries to a page.
 *
 * This function invalidates the given boot data entry by setting its
 * `is_valid` field to `kBootDataInvalidEntry` before writing it to the
 * flash.
 *
 * @param page Flash info page.
 * @param num_entries Number of entries to write.
 * @param boot_data A boot data entry.
 */
static void fill_with_invalidated_boot_data(flash_ctrl_info_page_t page,
                                            size_t num_entries,
                                            const boot_data_t *boot_data) {
  boot_data_t invalidated = *boot_data;
  invalidated.identifier = kBootDataIdentifier;
  invalidated.is_valid = kBootDataInvalidEntry;
  for (size_t i = 0; i < num_entries; ++i) {
    write_boot_data(page, i, &invalidated);
  }
}

/**
 * Compares two `boot_data_t` structs.
 *
 * @param lhs LHS of the comparison.
 * @param rhs RHS of the comparison.
 * @return The result of the operation.
 */
static rom_error_t compare_boot_data(const boot_data_t *lhs,
                                     const boot_data_t *rhs) {
  if (memcmp(lhs, rhs, sizeof(boot_data_t)) != 0) {
    return kErrorUnknown;
  }
  return kErrorOk;
}

/**
 * Checks whether a boot data entry is valid.
 *
 * This function checks the `identifier`, `digest`, and counter fields of a boot
 * data entry.
 *
 * @param boot_data A boot data entry.
 * @return The result of the operation.
 */
static rom_error_t check_boot_data(const boot_data_t *boot_data,
                                   uint32_t counter) {
  enum {
    kDigestRegionOffset = sizeof(boot_data->digest),
    kDigestRegionSize = sizeof(boot_data_t) - sizeof(boot_data->digest),
  };

  if (boot_data->identifier != kBootDataIdentifier) {
    return kErrorUnknown;
  }

  if (boot_data->counter != counter) {
    return kErrorUnknown;
  }

  hmac_digest_t act_digest;
  hmac_sha256_init();
  hmac_sha256_update((const char *)boot_data + kDigestRegionOffset,
                     kDigestRegionSize);
  hmac_sha256_final(&act_digest);
  if (memcmp(&act_digest, &boot_data->digest, sizeof(act_digest)) != 0) {
    return kErrorUnknown;
  }
  return kErrorOk;
}

rom_error_t check_test_data_test(void) {
  RETURN_IF_ERROR(check_boot_data(&kTestBootData, kTestBootData.counter));
  return kErrorOk;
}

rom_error_t read_empty_default_in_non_prod(void) {
  erase_boot_data_pages();

  boot_data_t boot_data;
  RETURN_IF_ERROR(boot_data_read(kLcStateTest, &boot_data));
  RETURN_IF_ERROR(check_boot_data(&boot_data, 5));
  return kErrorOk;
}

rom_error_t read_empty_default_in_prod(void) {
  erase_boot_data_pages();

  rom_error_t exp_error = kErrorBootDataNotFound;
  hardened_bool_t allowed_in_prod = otp_read32(
      OTP_CTRL_PARAM_CREATOR_SW_CFG_DEFAULT_BOOT_DATA_IN_PROD_EN_OFFSET);
  if (allowed_in_prod == kHardenedBoolTrue) {
    exp_error = kErrorOk;
  }

  boot_data_t boot_data;
  if (boot_data_read(kLcStateProd, &boot_data) == exp_error) {
    return kErrorOk;
  }
  return kErrorUnknown;
}

rom_error_t read_single_page_0_test(void) {
  erase_boot_data_pages();
  write_boot_data(kFlashCtrlInfoPageBootData0, 0, &kTestBootData);

  boot_data_t boot_data;
  RETURN_IF_ERROR(boot_data_read(kLcStateProd, &boot_data));
  RETURN_IF_ERROR(compare_boot_data(&boot_data, &kTestBootData));
  return kErrorOk;
}

rom_error_t read_single_page_1_test(void) {
  erase_boot_data_pages();
  write_boot_data(kFlashCtrlInfoPageBootData1, 0, &kTestBootData);

  boot_data_t boot_data;
  uint64_t start = ibex_mcycle_read();
  RETURN_IF_ERROR(boot_data_read(kLcStateProd, &boot_data));
  uint64_t end = ibex_mcycle_read();
  RETURN_IF_ERROR(compare_boot_data(&boot_data, &kTestBootData));
  if (end - start > UINT32_MAX) {
    LOG_FATAL("boot_data_read() took more than UINT32_MAX cycles");
    return kErrorUnknown;
  }
  uint32_t cycles = (uint32_t)(end - start);
  LOG_INFO("boot_data_read() took %u cycles", cycles);
  return kErrorOk;
}

rom_error_t read_full_page_0_test(void) {
  erase_boot_data_pages();
  fill_with_invalidated_boot_data(kFlashCtrlInfoPageBootData0,
                                  kBootDataEntriesPerPage - 1, &kTestBootData);
  write_boot_data(kFlashCtrlInfoPageBootData0, kBootDataEntriesPerPage - 1,
                  &kTestBootData);
  fill_with_invalidated_boot_data(kFlashCtrlInfoPageBootData1,
                                  kBootDataEntriesPerPage, &kTestBootData);

  boot_data_t boot_data;
  RETURN_IF_ERROR(boot_data_read(kLcStateProd, &boot_data));
  RETURN_IF_ERROR(compare_boot_data(&boot_data, &kTestBootData));
  return kErrorOk;
}

rom_error_t read_full_page_1_test(void) {
  erase_boot_data_pages();
  fill_with_invalidated_boot_data(kFlashCtrlInfoPageBootData0,
                                  kBootDataEntriesPerPage, &kTestBootData);
  fill_with_invalidated_boot_data(kFlashCtrlInfoPageBootData1,
                                  kBootDataEntriesPerPage - 1, &kTestBootData);
  write_boot_data(kFlashCtrlInfoPageBootData1, kBootDataEntriesPerPage - 1,
                  &kTestBootData);

  boot_data_t boot_data;
  uint64_t start = ibex_mcycle_read();
  RETURN_IF_ERROR(boot_data_read(kLcStateProd, &boot_data));
  uint64_t end = ibex_mcycle_read();
  RETURN_IF_ERROR(compare_boot_data(&boot_data, &kTestBootData));

  CHECK(end - start <= UINT32_MAX, "Cycle count must fit in uint32_t");
  uint32_t cycles = (uint32_t)(end - start);
  LOG_INFO("boot_data_read() took %u cycles", cycles);
  return kErrorOk;
}

rom_error_t write_empty_test(void) {
  erase_boot_data_pages();
  RETURN_IF_ERROR(boot_data_write(&kTestBootData));
  boot_data_t boot_data;
  RETURN_IF_ERROR(boot_data_read(kLcStateProd, &boot_data));
  RETURN_IF_ERROR(compare_boot_data(&kTestBootData, &boot_data));
  return kErrorOk;
}

rom_error_t write_page_switch_test(void) {
  erase_boot_data_pages();
  boot_data_t boot_data_act;
  boot_data_t boot_data_exp;
  uint32_t counter_exp = kBootDataDefaultCounterVal;

  // Write `kBootDataEntriesPerPage` + 1 entries to test the switch from page 0
  // to page 1.
  for (size_t i = 0; i < kBootDataEntriesPerPage + 1; ++i) {
    RETURN_IF_ERROR(boot_data_write(&kTestBootData));
    // Check `identifier`, `digest`, and `counter` fields.
    RETURN_IF_ERROR(boot_data_read(kLcStateProd, &boot_data_act));
    RETURN_IF_ERROR(check_boot_data(&boot_data_act, ++counter_exp));
    if (i > 0) {
      // Previous entry must be invalidated.
      boot_data_t prev_entry;
      read_boot_data(kFlashCtrlInfoPageBootData0, i - 1, &prev_entry);
      if (prev_entry.is_valid != kBootDataInvalidEntry) {
        LOG_ERROR("Previous entry was not invalidated");
        return kErrorUnknown;
      }
    }
  }
  // Last written entry must be at entry 0 in page 1.
  read_boot_data(kFlashCtrlInfoPageBootData1, 0, &boot_data_exp);
  if (memcmp(&boot_data_act, &boot_data_exp, sizeof(boot_data_t)) != 0) {
    LOG_ERROR("Page 0 -> 1 switch failed.");
    return kErrorUnknown;
  }

  // Write `kBootDataEntriesPerPage` entries to test the switch from page 1 to
  // page 0.
  for (size_t i = 1; i < kBootDataEntriesPerPage + 1; ++i) {
    RETURN_IF_ERROR(boot_data_write(&kTestBootData));
    // Check `identifier`, `digest`, and `counter` fields.
    RETURN_IF_ERROR(boot_data_read(kLcStateProd, &boot_data_act));
    RETURN_IF_ERROR(check_boot_data(&boot_data_act, ++counter_exp));
    // Previous entry must be invalidated.
    boot_data_t prev_entry;
    read_boot_data(kFlashCtrlInfoPageBootData1, i - 1, &prev_entry);
    if (prev_entry.is_valid != kBootDataInvalidEntry) {
      LOG_ERROR("Previous entry was not invalidated");
      return kErrorUnknown;
    }
  }
  // Last written entry must be at entry 0 in page 0.
  read_boot_data(kFlashCtrlInfoPageBootData0, 0, &boot_data_exp);
  if (memcmp(&boot_data_act, &boot_data_exp, sizeof(boot_data_t)) != 0) {
    LOG_ERROR("Page 1 -> 0 switch failed.");
    return kErrorUnknown;
  }

  return kErrorOk;
}

bool test_main(void) {
  status_t result = OK_STATUS();

  // Initialize the sec_mmio table so that we can run this test with both rom
  // and test_rom.
  sec_mmio_init();
  flash_ctrl_init();
  SEC_MMIO_WRITE_INCREMENT(kFlashCtrlSecMmioInit);
  sec_mmio_check_counters(/*expected_check_count=*/0);

  EXECUTE_TEST(result, check_test_data_test);
  EXECUTE_TEST(result, read_empty_default_in_non_prod);
  EXECUTE_TEST(result, read_empty_default_in_prod);
  EXECUTE_TEST(result, read_single_page_0_test);
  EXECUTE_TEST(result, read_single_page_1_test);
  EXECUTE_TEST(result, read_full_page_0_test);
  EXECUTE_TEST(result, read_full_page_1_test);
  EXECUTE_TEST(result, write_empty_test);
  EXECUTE_TEST(result, write_page_switch_test);

  return status_ok(result);
}
