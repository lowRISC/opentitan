// Copyright lowRISC contributors (OpenTitan project).
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
static const flash_ctrl_info_page_t *kPages[2] = {
    &kFlashCtrlInfoPageBootData0,
    &kFlashCtrlInfoPageBootData1,
};

enum {
  kCounter = (kBootDataDefaultCounterVal | 1) + 1,
};

/**
 * Boot data entry used in tests.
 */
boot_data_t kTestBootData0 = (boot_data_t){
    .digest = {{
        0x44e757cb,
        0x19899a04,
        0xf872d77f,
        0x58361229,
        0x48d748f1,
        0xfcafabf1,
        0x4fbc4153,
        0x0f05e1c9,
    }},
    .identifier = kBootDataIdentifier,
    .version = kBootDataVersion2,
    .is_valid = kBootDataValidEntry,
    .counter = kCounter,
    .min_security_version_rom_ext = 0,
    .primary_bl0_slot = kBootSlotA,
};

boot_data_t kTestBootData1 = (boot_data_t){
    .digest = {{
        0x3bc88432,
        0xafdb9475,
        0x38f9d68c,
        0x19919156,
        0xe8e065d3,
        0xf88568b8,
        0xd9d49849,
        0xe3ae6d8d,
    }},
    .identifier = kBootDataIdentifier,
    .version = kBootDataVersion2,
    .is_valid = kBootDataValidEntry,
    .counter = kCounter + 1,
    .min_security_version_rom_ext = 0,
    .primary_bl0_slot = kBootSlotA,
};

/**
 * Sets/Unsets ecc and scramble settings for boot data pages.
 *
 * @param enable New ecc and scramble settings.
 */
static void boot_data_pages_cfg_set(hardened_bool_t enable) {
  uint8_t mubi_en =
      enable == kHardenedBoolTrue ? kMultiBitBool4True : kMultiBitBool4False;
  for (size_t i = 0; i < ARRAYSIZE(kPages); ++i) {
    flash_ctrl_info_cfg_set(kPages[i], (flash_ctrl_cfg_t){
                                           .scrambling = mubi_en,
                                           .ecc = mubi_en,
                                           .he = kMultiBitBool4False,
                                       });
  }
}

/**
 * Sets read, write, and erase permissions for boot data pages.
 *
 * This function is intended for backdoor access during tests, e.g. to set the
 * contents of a page before a read test or check the contents after a write
 * test.
 *
 * @param perm New read, write, and erase permissions.
 */
static void boot_data_pages_mp_set(hardened_bool_t perm) {
  uint8_t mubi_perm =
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
static void write_boot_data(const flash_ctrl_info_page_t *page, size_t index,
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
 * Writes a boot data entry at the given page multiple times.

 * This function is used to write the same boot data entry to multiple indices
 * of a flash info page, as specified by a bitmap.
 *
 * @param page Flash info page.
 * @param bitmap A bitmap where each bit represents an index in the page.
 * @param boot_data A boot data entry.
 */
static void write_dup_boot_data(const flash_ctrl_info_page_t *page,
                                uint32_t bitmap, const boot_data_t *boot_data) {
  boot_data_t invalid = {0};
  for (size_t i = 0; i < kBootDataEntriesPerPage && bitmap; ++i) {
    if (bitmap & 1) {
      write_boot_data(page, i, boot_data);
    } else {
      write_boot_data(page, i, &invalid);
    }
    bitmap >>= 1;
  }
}

/**
 * Reads the boot data entry at the given page and index.
 *
 * @param page Flash info page.
 * @param index Index of the entry to read in the given page.
 * @param boot_data A boot data entry.
 */
static void read_boot_data(const flash_ctrl_info_page_t *page, size_t index,
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
static void fill_with_invalidated_boot_data(const flash_ctrl_info_page_t *page,
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

  hmac_digest_t exp_digest;
  hmac_sha256((const char *)boot_data + kDigestRegionOffset, kDigestRegionSize,
              &exp_digest);
  if (memcmp(&exp_digest, &boot_data->digest, sizeof(exp_digest)) != 0) {
    return kErrorUnknown;
  }
  return kErrorOk;
}

/**
 * Checks whether boot data entries is valid with dual redundancy scheme.
 *
 * This function checks the `identifier`, `digest`, and counter fields of a boot
 * data entry.
 *
 * @param counter_0 expected counter of entry on page 0.
 * @return The result of the operation.
 */
static rom_error_t check_boot_data_redundency(uint32_t page, uint32_t equals) {
  boot_data_t boot_data_0;
  boot_data_t boot_data_1;
  // Check `identifier`, `digest`, and `counter` fields.
  read_boot_data(kPages[0], 0, &boot_data_0);
  RETURN_IF_ERROR(check_boot_data(&boot_data_0, equals ^ page));
  read_boot_data(kPages[0], 1, &boot_data_0);
  RETURN_IF_ERROR(check_boot_data(&boot_data_0, equals ^ page));
  LOG_INFO("Page 0 OK");
  read_boot_data(kPages[1], 0, &boot_data_1);
  RETURN_IF_ERROR(check_boot_data(&boot_data_1, equals ^ page ^ 1));
  read_boot_data(kPages[1], 1, &boot_data_1);
  RETURN_IF_ERROR(check_boot_data(&boot_data_1, equals ^ page ^ 1));
  LOG_INFO("Page 1 OK");
  RETURN_IF_ERROR(boot_data_redundancy_check());

  // read the boot data with boot_data_read and compare with the newer one.
  boot_data_t boot_data;
  RETURN_IF_ERROR(boot_data_read(kLcStateProd, &boot_data));
  if (boot_data_0.counter > boot_data_1.counter) {
    RETURN_IF_ERROR(compare_boot_data(&boot_data, &boot_data_0));
  } else {
    RETURN_IF_ERROR(compare_boot_data(&boot_data, &boot_data_1));
  }

  return kErrorOk;
}

rom_error_t check_test_data_test(void) {
  RETURN_IF_ERROR(check_boot_data(&kTestBootData0, kTestBootData0.counter));
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
  write_boot_data(kPages[0], 0, &kTestBootData0);

  boot_data_t boot_data;
  RETURN_IF_ERROR(boot_data_read(kLcStateProd, &boot_data));
  RETURN_IF_ERROR(compare_boot_data(&boot_data, &kTestBootData0));
  return kErrorOk;
}

rom_error_t read_single_page_1_test(void) {
  erase_boot_data_pages();
  write_boot_data(kPages[1], 0, &kTestBootData0);

  boot_data_t boot_data;
  uint64_t start = ibex_mcycle_read();
  RETURN_IF_ERROR(boot_data_read(kLcStateProd, &boot_data));
  uint64_t end = ibex_mcycle_read();
  RETURN_IF_ERROR(compare_boot_data(&boot_data, &kTestBootData0));
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
  fill_with_invalidated_boot_data(kPages[0], kBootDataEntriesPerPage - 1,
                                  &kTestBootData0);
  write_boot_data(kPages[0], kBootDataEntriesPerPage - 1, &kTestBootData0);
  fill_with_invalidated_boot_data(kPages[1], kBootDataEntriesPerPage,
                                  &kTestBootData0);

  boot_data_t boot_data;
  RETURN_IF_ERROR(boot_data_read(kLcStateProd, &boot_data));
  RETURN_IF_ERROR(compare_boot_data(&boot_data, &kTestBootData0));
  return kErrorOk;
}

rom_error_t read_full_page_1_test(void) {
  erase_boot_data_pages();
  fill_with_invalidated_boot_data(kPages[0], kBootDataEntriesPerPage,
                                  &kTestBootData0);
  fill_with_invalidated_boot_data(kPages[1], kBootDataEntriesPerPage - 1,
                                  &kTestBootData0);
  write_boot_data(kPages[1], kBootDataEntriesPerPage - 1, &kTestBootData0);

  boot_data_t boot_data;
  uint64_t start = ibex_mcycle_read();
  RETURN_IF_ERROR(boot_data_read(kLcStateProd, &boot_data));
  uint64_t end = ibex_mcycle_read();
  RETURN_IF_ERROR(compare_boot_data(&boot_data, &kTestBootData0));

  CHECK(end - start <= UINT32_MAX, "Cycle count must fit in uint32_t");
  uint32_t cycles = (uint32_t)(end - start);
  LOG_INFO("boot_data_read() took %u cycles", cycles);
  return kErrorOk;
}

/**
 * Tests the read function with different states of the dual-redundancy scheme.
 *
 * This test iterates through all possible valid/invalid combinations of entries
 * on both pages and ensures that the most recent (highest counter) valid entry
 * is always selected.
 */
rom_error_t read_redundancy_test(void) {
  uint32_t bitmaps[2];
  for (uint32_t a = 0; a <= 1; ++a) {  // page index variable
    uint32_t b = !a;
    for (bitmaps[a] = 0; bitmaps[a] <= 3; ++bitmaps[a]) {
      for (bitmaps[b] = 0; bitmaps[b] <= 3; ++bitmaps[b]) {
        if (bitmaps[a] == 0 && bitmaps[b] == 0) {
          // Skip the case where all entries are invalid.
          continue;
        }
        erase_boot_data_pages();
        write_dup_boot_data(kPages[a], bitmaps[a], &kTestBootData0);
        write_dup_boot_data(kPages[b], bitmaps[b], &kTestBootData1);
        boot_data_t boot_data;
        RETURN_IF_ERROR(boot_data_read(kLcStateProd, &boot_data));
        if (bitmaps[b]) {
          // At least one valid entry in page B. The boot_data_read
          // should prioritize the larger counter.
          RETURN_IF_ERROR(compare_boot_data(&boot_data, &kTestBootData1));
        } else {
          RETURN_IF_ERROR(compare_boot_data(&boot_data, &kTestBootData0));
        }
      }
    }
  }
  return kErrorOk;
}

rom_error_t write_default_disallowed_test(void) {
  erase_boot_data_pages();
  boot_data_t boot_data = kTestBootData0;
  boot_data.counter = kBootDataDefaultCounterVal;
  CHECK(boot_data_write(&boot_data) == kErrorBootDataInvalid);
  return kErrorOk;
}

// Tests the write function when both pages are empty.
// This test also validates that the data was correctly duplicated across both
// pages according to the dual-redundancy scheme.
rom_error_t write_empty_test(void) {
  erase_boot_data_pages();
  RETURN_IF_ERROR(boot_data_write(&kTestBootData0));
  RETURN_IF_ERROR(boot_data_redundancy_check());

  boot_data_t boot_data;
  read_boot_data(kPages[0], 0, &boot_data);
  RETURN_IF_ERROR(compare_boot_data(&kTestBootData0, &boot_data));
  read_boot_data(kPages[0], 1, &boot_data);
  RETURN_IF_ERROR(compare_boot_data(&kTestBootData0, &boot_data));
  LOG_INFO("Page 0 OK");

  read_boot_data(kPages[1], 0, &boot_data);
  RETURN_IF_ERROR(compare_boot_data(&kTestBootData1, &boot_data));
  read_boot_data(kPages[1], 1, &boot_data);
  RETURN_IF_ERROR(compare_boot_data(&kTestBootData1, &boot_data));
  LOG_INFO("Page 1 OK");

  RETURN_IF_ERROR(boot_data_read(kLcStateProd, &boot_data));
  RETURN_IF_ERROR(compare_boot_data(&kTestBootData1, &boot_data));
  return kErrorOk;
}

// Tests the write function where both pages are valid and page 1 is active.
// Page 0 should be written first.
rom_error_t write_page_1_active_test(void) {
  for (uint32_t bitmap = 1; bitmap <= 3; ++bitmap) {
    erase_boot_data_pages();
    write_dup_boot_data(kPages[0], bitmap, &kTestBootData0);
    write_dup_boot_data(kPages[1], bitmap, &kTestBootData1);  // active page
    RETURN_IF_ERROR(boot_data_redundancy_check());

    RETURN_IF_ERROR(boot_data_write(&kTestBootData0));
    RETURN_IF_ERROR(
        check_boot_data_redundency(/*page=*/0, /*equals=*/kCounter + 2));
  }
  return kErrorOk;
}

// Tests the write function where both pages are valid and page 0 is active.
// Page 1 should be written first.
rom_error_t write_page_0_active_test(void) {
  for (uint32_t bitmap = 1; bitmap <= 3; ++bitmap) {
    erase_boot_data_pages();
    write_dup_boot_data(kPages[0], bitmap, &kTestBootData1);  // active page
    write_dup_boot_data(kPages[1], bitmap, &kTestBootData0);
    RETURN_IF_ERROR(boot_data_redundancy_check());

    RETURN_IF_ERROR(boot_data_write(&kTestBootData0));
    RETURN_IF_ERROR(
        check_boot_data_redundency(/*page=*/1, /*equals=*/kCounter + 2));
  }
  return kErrorOk;
}

// Tests the write func where the previous pages are: empty/valid.
// Page 0 should be written first.
rom_error_t write_page_0_missing_test(void) {
  for (uint32_t bitmap = 1; bitmap <= 3; ++bitmap) {
    erase_boot_data_pages();
    write_dup_boot_data(kPages[1], bitmap, &kTestBootData1);  // active page
    CHECK(boot_data_redundancy_check() == kErrorBootDataInvalid);

    RETURN_IF_ERROR(boot_data_write(&kTestBootData0));
    RETURN_IF_ERROR(
        check_boot_data_redundency(/*page=*/0, /*equals=*/kCounter + 2));
  }
  return kErrorOk;
}

// Tests the write func where the previous pages are: valid/empty.
// Page 1 should be written first.
rom_error_t write_page_1_missing_test(void) {
  for (uint32_t bitmap = 1; bitmap <= 3; ++bitmap) {
    erase_boot_data_pages();
    write_dup_boot_data(kPages[0], bitmap, &kTestBootData0);  // active page
    CHECK(boot_data_redundancy_check() == kErrorBootDataInvalid);

    RETURN_IF_ERROR(boot_data_write(&kTestBootData0));
    RETURN_IF_ERROR(
        check_boot_data_redundency(/*page=*/1, /*equals=*/kCounter + 2));
  }
  return kErrorOk;
}

// Tests the write func where the previous pages are: corrupt/valid.
// Page 0 should be written first.
rom_error_t write_page_0_invalid_test(void) {
  for (uint32_t bitmap = 1; bitmap <= 3; ++bitmap) {
    erase_boot_data_pages();
    write_dup_boot_data(kPages[1], bitmap, &kTestBootData1);  // active page
    fill_with_invalidated_boot_data(kPages[0], 2, &kTestBootData0);
    CHECK(boot_data_redundancy_check() == kErrorBootDataInvalid);

    RETURN_IF_ERROR(boot_data_write(&kTestBootData0));
    RETURN_IF_ERROR(
        check_boot_data_redundency(/*page=*/0, /*equals=*/kCounter + 2));
  }
  return kErrorOk;
}

// Tests the write func where the previous pages are: valid/corrupt.
// Page 1 should be written first.
rom_error_t write_page_1_invalid_test(void) {
  for (uint32_t bitmap = 1; bitmap <= 3; ++bitmap) {
    erase_boot_data_pages();
    write_dup_boot_data(kPages[0], bitmap, &kTestBootData0);  // active page
    fill_with_invalidated_boot_data(kPages[1], 2, &kTestBootData0);
    CHECK(boot_data_redundancy_check() == kErrorBootDataInvalid);

    RETURN_IF_ERROR(boot_data_write(&kTestBootData0));
    RETURN_IF_ERROR(
        check_boot_data_redundency(/*page=*/1, /*equals=*/kCounter + 2));
  }
  return kErrorOk;
}

// Tests the write func compatibilty when switching between the old circular
// buffer scheme and the new dual-redundancy scheme.
static rom_error_t write_page_compatibility_test_impl(void) {
  erase_boot_data_pages();
  boot_data_t boot_data;

  // Prepare the boot data with old circular buffer scheme.
  // Write `kBootDataEntriesPerPage` * 2 + 3 entries.
  for (size_t i = 0; i < kBootDataEntriesPerPage * 2 + 3; ++i) {
    RETURN_IF_ERROR(boot_data_write_old(&kTestBootData0));
    CHECK(boot_data_redundancy_check() == kErrorBootDataInvalid);
  }

  // Switch to new dual-redundancy scheme
  uint32_t counter = kTestBootData0.counter + kBootDataEntriesPerPage * 2 + 4;
  RETURN_IF_ERROR(boot_data_write(&kTestBootData0));
  RETURN_IF_ERROR(boot_data_read(kLcStateProd, &boot_data));
  RETURN_IF_ERROR(check_boot_data(&boot_data, counter + 1));
  RETURN_IF_ERROR(
      check_boot_data_redundency(/*page=*/1, /*equals=*/counter + 0));

  // Update with new dual-redundancy scheme
  RETURN_IF_ERROR(boot_data_write(&kTestBootData0));
  RETURN_IF_ERROR(boot_data_read(kLcStateProd, &boot_data));
  RETURN_IF_ERROR(check_boot_data(&boot_data, counter + 3));
  RETURN_IF_ERROR(
      check_boot_data_redundency(/*page=*/1, /*equals=*/counter + 2));

  // Switch back to old circular scheme
  for (size_t i = 0; i < kBootDataEntriesPerPage * 2 + 3; ++i) {
    RETURN_IF_ERROR(boot_data_write_old(&kTestBootData0));
    RETURN_IF_ERROR(boot_data_read(kLcStateProd, &boot_data));
    RETURN_IF_ERROR(check_boot_data(&boot_data, counter + 4 + i));
  }

  return kErrorOk;
}

rom_error_t write_page_compatibility_test(void) {
  return write_page_compatibility_test_impl();
}

rom_error_t write_page_compatibility_test_with_ecc(void) {
  boot_data_pages_cfg_set(kHardenedBoolTrue);
  rom_error_t result = write_page_compatibility_test_impl();
  boot_data_pages_cfg_set(kHardenedBoolFalse);
  return result;
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
  EXECUTE_TEST(result, read_redundancy_test);
  EXECUTE_TEST(result, write_default_disallowed_test);
  EXECUTE_TEST(result, write_empty_test);
  EXECUTE_TEST(result, write_page_1_active_test);
  EXECUTE_TEST(result, write_page_0_active_test);
  EXECUTE_TEST(result, write_page_0_missing_test);
  EXECUTE_TEST(result, write_page_1_missing_test);
  EXECUTE_TEST(result, write_page_0_invalid_test);
  EXECUTE_TEST(result, write_page_1_invalid_test);
  EXECUTE_TEST(result, write_page_compatibility_test);
  EXECUTE_TEST(result, write_page_compatibility_test_with_ecc);

  return status_ok(result);
}
