// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/rand_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

enum {
  kFlashInfoPageIdCreatorSecret = 1,
  kFlashInfoPageIdOwnerSecret = 2,
  kFlashInfoPageIdIsoPart = 3,
  kFlashInfoBank = 0,
  kFlashDataBank0 = 0,
  kFlashDataBank1 = 1,
  kRegionBaseBank0Page0Index = 0,
  kRegionBaseBank1Page0Index = 256,
  kRegionBaseBank1Page255Index = 511,
  kFlashBank0DataRegion = 0,
  kFlashBank1DataRegion = 1,
  kPartitionId = 0,
  kRegionSize = 1,
  kDataSize = 16,
  kPageSize = 2048,
  kNumLoops = 10,
};

static dif_flash_ctrl_state_t flash_state;
static uint32_t test_data[kDataSize];

/**
 * Check data read from host interface against known data.
 */
static void read_and_check_host_if(uint32_t addr, const uint32_t *check_data) {
  mmio_region_t flash_addr =
      mmio_region_from_addr(TOP_EARLGREY_EFLASH_BASE_ADDR + addr);
  uint32_t host_data[kDataSize];
  for (int i = 0; i < kDataSize; ++i) {
    host_data[i] =
        mmio_region_read32(flash_addr, i * (ptrdiff_t)sizeof(uint32_t));
  }
  CHECK_ARRAYS_EQ(host_data, check_data, kDataSize);
}

/**
 * Tests the erase, write and
 * read of the specified information partition.
 * Confirms that the written data is read back correctly.
 */
static void do_info_partition_test(uint32_t partition_number) {
  uint32_t address = 0;
  CHECK_STATUS_OK(flash_ctrl_testutils_info_region_setup(
      &flash_state, partition_number, kFlashInfoBank, kPartitionId, &address));

  for (int i = 0; i < kDataSize; ++i) {
    test_data[i] = rand_testutils_gen32();
  }

  CHECK_STATUS_OK(flash_ctrl_testutils_erase_page(
      &flash_state, address, kPartitionId, kDifFlashCtrlPartitionTypeInfo));
  CHECK_STATUS_OK(
      flash_ctrl_testutils_write(&flash_state, address, kPartitionId, test_data,
                                 kDifFlashCtrlPartitionTypeInfo, kDataSize));

  uint32_t readback_data[kDataSize];
  CHECK_STATUS_OK(flash_ctrl_testutils_read(
      &flash_state, address, kPartitionId, readback_data,
      kDifFlashCtrlPartitionTypeInfo, kDataSize, 0));

  CHECK_ARRAYS_EQ(readback_data, test_data, kDataSize);
}

/**
 * Tests the erase, write and read of the lowest and highest page of
 * bank 1 data partition or the reads for the lowest page of bank 0.
 * For bank 1 confirms that the written data is read back correctly.
 */
static void do_data_partition_test(uint32_t bank_number) {
  if (bank_number == 0) {
    // Bank 0 contains the program data so can only be read and checked
    // against the host interface read.
    uint32_t address = 0;
    CHECK_STATUS_OK(flash_ctrl_testutils_data_region_setup(
        &flash_state, kRegionBaseBank0Page0Index, kFlashBank0DataRegion,
        kRegionSize, &address));

    uint32_t readback_data[kDataSize];
    CHECK_STATUS_OK(flash_ctrl_testutils_read(
        &flash_state, address, kPartitionId, readback_data,
        kDifFlashCtrlPartitionTypeData, kDataSize, 0));

    read_and_check_host_if(kRegionBaseBank0Page0Index, readback_data);
  } else if (bank_number == 1) {
    for (int i = 0; i < 2; ++i) {
      uint32_t page_index =
          (i == 0) ? kRegionBaseBank1Page0Index : kRegionBaseBank1Page255Index;
      for (int j = 0; j < kDataSize; ++j) {
        test_data[i] = rand_testutils_gen32();
      }
      uint32_t address = 0;
      CHECK_STATUS_OK(flash_ctrl_testutils_data_region_setup(
          &flash_state, page_index, kFlashBank1DataRegion, kRegionSize,
          &address));
      CHECK_STATUS_OK(flash_ctrl_testutils_erase_page(
          &flash_state, address, kPartitionId, kDifFlashCtrlPartitionTypeData));
      CHECK_STATUS_OK(flash_ctrl_testutils_write(
          &flash_state, address, kPartitionId, test_data,
          kDifFlashCtrlPartitionTypeData, kDataSize));

      uint32_t readback_data[kDataSize];
      CHECK_STATUS_OK(flash_ctrl_testutils_read(
          &flash_state, address, kPartitionId, readback_data,
          kDifFlashCtrlPartitionTypeData, kDataSize, 1));
      read_and_check_host_if(kPageSize * page_index, test_data);
      CHECK_ARRAYS_EQ(readback_data, test_data, kDataSize);
    }
  } else {
    LOG_ERROR("Unexpected bank number, only 0 and 1 are valid.");
  }
}

bool test_main(void) {
  dif_clkmgr_t clkmgr;
  CHECK_DIF_OK(dif_clkmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR), &clkmgr));

  CHECK_DIF_OK(dif_clkmgr_jitter_set_enabled(&clkmgr, kDifToggleEnabled));

  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash_state,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));

  for (int i = 0; i < kNumLoops; ++i) {
    do_info_partition_test(kFlashInfoPageIdCreatorSecret);
    do_info_partition_test(kFlashInfoPageIdOwnerSecret);
    do_info_partition_test(kFlashInfoPageIdIsoPart);
    do_data_partition_test(kFlashDataBank0);
    do_data_partition_test(kFlashDataBank1);
  }

  return true;
}
