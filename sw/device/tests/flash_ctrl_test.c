// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define CHECK_EQZ(x) CHECK((x) == 0)
#define CHECK_NEZ(x) CHECK((x) != 0)

static dif_flash_ctrl_device_info_t flash_info;
#define FLASH_WORD_SZ flash_info.bytes_per_word
#define FLASH_PAGE_SZ flash_info.bytes_per_page
#define FLASH_UINT32_WORDS_PER_PAGE \
  (FLASH_PAGE_SZ / FLASH_WORD_SZ) * (FLASH_WORD_SZ / sizeof(uint32_t))
#define FLASH_PAGES_PER_BANK flash_info.data_pages

static dif_flash_ctrl_state_t flash;

/*
 * Basic test of page erase / program / read functions. Tests pages from both
 * the data and info partitions.
 */
static void test_basic_io(void) {
  // The info partitions have no default access. Specifically set up a region.
  dif_flash_ctrl_info_region_t info_region = {
      .bank = 1, .partition_id = 0, .page = 0};
  dif_flash_ctrl_region_properties_t region_properties = {
      .rd_en = kMultiBitBool4True,
      .prog_en = kMultiBitBool4True,
      .erase_en = kMultiBitBool4True,
      .scramble_en = kMultiBitBool4True,
      .ecc_en = kMultiBitBool4True,
      .high_endurance_en = kMultiBitBool4False};
  CHECK_DIF_OK(dif_flash_ctrl_set_info_region_properties(&flash, info_region,
                                                         region_properties));
  CHECK_DIF_OK(dif_flash_ctrl_set_info_region_enablement(&flash, info_region,
                                                         kDifToggleEnabled));

  // Also set up data region to enable scrambling.
  region_properties.rd_en = kMultiBitBool4True;
  region_properties.prog_en = kMultiBitBool4True;
  region_properties.erase_en = kMultiBitBool4True;

  dif_flash_ctrl_data_region_properties_t data_region = {
      .base = FLASH_PAGES_PER_BANK,
      .size = 0x1,
      .properties = region_properties};

  CHECK_DIF_OK(
      dif_flash_ctrl_set_data_region_properties(&flash, 0, data_region));
  CHECK_DIF_OK(
      dif_flash_ctrl_set_data_region_enablement(&flash, 0, kDifToggleEnabled));

  ptrdiff_t flash_bank_1_addr =
      (ptrdiff_t)flash_info.data_pages * (ptrdiff_t)flash_info.bytes_per_page;
  mmio_region_t flash_bank_1 = mmio_region_from_addr(
      TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR + (uintptr_t)flash_bank_1_addr);

  // Test erasing flash data partition; this should turn the whole bank to all
  // ones.
  CHECK_STATUS_OK(flash_ctrl_testutils_erase_page(
      &flash, (uint32_t)flash_bank_1_addr,
      /*partition_id=*/0, kDifFlashCtrlPartitionTypeData));
  for (int i = 0; i < FLASH_UINT32_WORDS_PER_PAGE; ++i) {
    CHECK_EQZ(
        ~mmio_region_read32(flash_bank_1, i * (ptrdiff_t)sizeof(uint32_t)));
  }

  // Erasing flash info partition 0; this should turn one page to all ones.
  CHECK_STATUS_OK(flash_ctrl_testutils_erase_page(
      &flash, (uint32_t)flash_bank_1_addr,
      /*partition_id=*/0, kDifFlashCtrlPartitionTypeInfo));

  // Prepare an entire page of non-trivial data to program into flash.
  uint32_t input_page[FLASH_UINT32_WORDS_PER_PAGE];
  uint32_t output_page[FLASH_UINT32_WORDS_PER_PAGE];
  CHECK(sizeof(input_page) == flash_info.bytes_per_page,
        "Unexpected buffer size. got: %d, want: %d", sizeof(input_page),
        flash_info.bytes_per_page);
  CHECK(sizeof(output_page) == flash_info.bytes_per_page,
        "Unexpected buffer size. got: %d, want: %d", sizeof(input_page),
        flash_info.bytes_per_page);
  memset(input_page, 0xa5, FLASH_UINT32_WORDS_PER_PAGE * sizeof(uint32_t));
  for (int i = 0; i < FLASH_UINT32_WORDS_PER_PAGE; i += 2) {
    input_page[i] ^= 0xffffffff;
  }

  // Attempt to live-program an entire page, where the overall payload is much
  // larger than the internal flash FIFO.
  CHECK_STATUS_OK(flash_ctrl_testutils_erase_and_write_page(
      &flash, (uint32_t)flash_bank_1_addr, /*partition_id=*/0, input_page,
      kDifFlashCtrlPartitionTypeData, FLASH_UINT32_WORDS_PER_PAGE));
  CHECK_STATUS_OK(flash_ctrl_testutils_read(
      &flash, (uint32_t)flash_bank_1_addr, /*partition_id=*/0, output_page,
      kDifFlashCtrlPartitionTypeData, FLASH_UINT32_WORDS_PER_PAGE,
      /*delay=*/0));
  CHECK_ARRAYS_EQ(output_page, input_page, FLASH_UINT32_WORDS_PER_PAGE);

  // Check from host side also.
  for (int i = 0; i < FLASH_UINT32_WORDS_PER_PAGE; i++) {
    output_page[i] =
        mmio_region_read32(flash_bank_1, i * (ptrdiff_t)sizeof(uint32_t));
  }
  CHECK_ARRAYS_EQ(output_page, input_page, FLASH_UINT32_WORDS_PER_PAGE);

  // Similar check for info page.
  CHECK_STATUS_OK(flash_ctrl_testutils_erase_and_write_page(
      &flash, (uint32_t)flash_bank_1_addr, /*partition_id=*/0, input_page,
      kDifFlashCtrlPartitionTypeInfo, FLASH_UINT32_WORDS_PER_PAGE));
  CHECK_STATUS_OK(flash_ctrl_testutils_read(
      &flash, (uint32_t)flash_bank_1_addr, /*partition_id=*/0, output_page,
      kDifFlashCtrlPartitionTypeInfo, FLASH_UINT32_WORDS_PER_PAGE,
      /*delay=*/0));
  CHECK_ARRAYS_EQ(output_page, input_page, FLASH_UINT32_WORDS_PER_PAGE);

  // Set up default access for data partitions.
  CHECK_STATUS_OK(flash_ctrl_testutils_default_region_access(
      &flash, /*rd_en=*/true, /*prog_en=*/true, /*erase_en=*/true,
      /*scramble_en=*/false, /*ecc_en=*/false, /*high_endurance_en=*/false));

  // Perform similar test on the last page of the first bank.
  ptrdiff_t flash_bank_0_last_page_addr =
      flash_bank_1_addr - (ptrdiff_t)FLASH_PAGE_SZ;
  mmio_region_t flash_bank_0_last_page =
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR +
                            (uintptr_t)flash_bank_0_last_page_addr);
  CHECK_STATUS_OK(flash_ctrl_testutils_erase_page(
      &flash, (uint32_t)flash_bank_0_last_page_addr,
      /*partition_id=*/0, kDifFlashCtrlPartitionTypeData));
  for (int i = 0; i < FLASH_UINT32_WORDS_PER_PAGE; ++i) {
    CHECK_EQZ(~mmio_region_read32(flash_bank_0_last_page,
                                  i * (ptrdiff_t)sizeof(uint32_t)));
  }

  CHECK_STATUS_OK(flash_ctrl_testutils_write(
      &flash, (uint32_t)flash_bank_0_last_page_addr, /*partition_id=*/0,
      input_page, kDifFlashCtrlPartitionTypeData, FLASH_UINT32_WORDS_PER_PAGE));
  CHECK_STATUS_OK(flash_ctrl_testutils_read(
      &flash, (uint32_t)flash_bank_0_last_page_addr,
      /*partition_id=*/0, output_page, kDifFlashCtrlPartitionTypeData,
      FLASH_UINT32_WORDS_PER_PAGE, /*delay=*/0));

  CHECK_ARRAYS_EQ(output_page, input_page, FLASH_UINT32_WORDS_PER_PAGE);
}

static void test_memory_protection(void) {
  dif_flash_ctrl_state_t flash;
  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash, mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));

  // Set up default access for data partitions.
  CHECK_STATUS_OK(flash_ctrl_testutils_default_region_access(
      &flash, /*rd_en=*/true, /*prog_en=*/true, /*erase_en=*/true,
      /*scramble_en=*/false, /*ecc_en=*/false, /*high_endurance_en=*/false));

  // A memory protection region representing the first page of the second bank.
  dif_flash_ctrl_region_properties_t protected_properties = {
      .rd_en = kMultiBitBool4True,
      .prog_en = kMultiBitBool4True,
      .erase_en = kMultiBitBool4True,
      .scramble_en = kMultiBitBool4False,
      .ecc_en = kMultiBitBool4True,
      .high_endurance_en = kMultiBitBool4False};

  dif_flash_ctrl_data_region_properties_t protected_region = {
      .base = FLASH_PAGES_PER_BANK,
      .size = 0x1,
      .properties = protected_properties};

  uintptr_t ok_region_start = TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR +
                              (protected_region.base * FLASH_PAGE_SZ);
  uintptr_t ok_region_end =
      ok_region_start + (protected_region.size * FLASH_PAGE_SZ);
  mmio_region_t ok_region = mmio_region_from_addr(ok_region_start);

  uintptr_t bad_region_start = ok_region_end;

  // Erase good and bad regions.
  CHECK_STATUS_OK(flash_ctrl_testutils_erase_page(
      &flash, ok_region_start,
      /*partition_id=*/0, kDifFlashCtrlPartitionTypeData));
  CHECK_STATUS_OK(flash_ctrl_testutils_erase_page(
      &flash, bad_region_start,
      /*partition_id=*/0, kDifFlashCtrlPartitionTypeData));

  // Turn off flash access by default.
  CHECK_STATUS_OK(flash_ctrl_testutils_default_region_access(
      &flash, /*rd_en=*/false, /*prog_en=*/false, /*erase_en=*/false,
      /*scramble_en=*/false, /*ecc_en=*/false, /*high_endurance_en=*/false));

  // Enable protected region for access.
  CHECK_DIF_OK(
      dif_flash_ctrl_set_data_region_properties(&flash, 0, protected_region));

  // Attempt to perform a write.
  uintptr_t region_boundary_start = bad_region_start - (FLASH_WORD_SZ * 2);
  mmio_region_t region_boundary = mmio_region_from_addr(region_boundary_start);

  // Place half the words in the good region and half in the bad.
  uint32_t words[(FLASH_WORD_SZ * 2 * 2) / sizeof(uint32_t)];
  memset(words, 0xa5, ARRAYSIZE(words) * sizeof(uint32_t));
  for (uint32_t i = 0; i < ARRAYSIZE(words); ++i) {
    words[i] += i;
  }

  // Perform a partial write.
  CHECK(status_err(flash_ctrl_testutils_write(
      &flash, region_boundary_start, /*partition_id=*/0, words,
      kDifFlashCtrlPartitionTypeData, ARRAYSIZE(words))));
  // Words in the good region should still match, while words in the bad region
  // should be all-ones, since we erased.
  for (int i = 0; i < ARRAYSIZE(words); ++i) {
    uint32_t expected = 0xffffffff;
    if (i < ARRAYSIZE(words) / 2) {
      expected = words[i];
    }
    CHECK(mmio_region_read32(region_boundary,
                             i * (ptrdiff_t)sizeof(uint32_t)) == expected);
  }

  // Attempt to erase bad page, which should fail.
  CHECK(status_err(flash_ctrl_testutils_erase_page(
      &flash, bad_region_start,
      /*partition_id=*/0, kDifFlashCtrlPartitionTypeData)));

  // Attempt to erase the good page, which should succeed.
  CHECK_STATUS_OK(flash_ctrl_testutils_erase_page(
      &flash, ok_region_start,
      /*partition_id=*/0, kDifFlashCtrlPartitionTypeData));
  for (int i = 0; i < FLASH_UINT32_WORDS_PER_PAGE; i++) {
    CHECK_EQZ(~mmio_region_read32(ok_region, i * (ptrdiff_t)sizeof(uint32_t)));
  }
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  flash_info = dif_flash_ctrl_get_device_info();
  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash, mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
  CHECK_STATUS_OK(flash_ctrl_testutils_wait_for_init(&flash));

  LOG_INFO("flash test!");

  CHECK_DIF_OK(dif_flash_ctrl_set_bank_erase_enablement(&flash, /*bank=*/0,
                                                        kDifToggleEnabled));
  CHECK_DIF_OK(dif_flash_ctrl_set_bank_erase_enablement(&flash, /*bank=*/1,
                                                        kDifToggleEnabled));

  test_basic_io();
  test_memory_protection();

  CHECK_DIF_OK(dif_flash_ctrl_set_bank_erase_enablement(&flash, /*bank=*/0,
                                                        kDifToggleDisabled));
  CHECK_DIF_OK(dif_flash_ctrl_set_bank_erase_enablement(&flash, /*bank=*/1,
                                                        kDifToggleDisabled));

  return true;
}
