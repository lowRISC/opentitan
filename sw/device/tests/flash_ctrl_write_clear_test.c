// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/boot_stage.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/base/chip.h"

#include "flash_ctrl_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// See chip_sw_flash_ctrl_write_clear in chip_flash_ctrl_testplan.hjson for
// test description.

OTTF_DEFINE_TEST_CONFIG();

enum {
  // Some dif_flash_ctrl functions don't require the partition parameter when
  // interacting with data partitions. This constant is added to improve
  // readability.
  kUnusedDataPartitionParam = 0,

  // Number of bytes per page.
  kFlashBytesPerPage = FLASH_CTRL_PARAM_BYTES_PER_PAGE,

  // Number of pages allocated to the ROM_EXT. The same number of pages are
  // allocated at the begining of each data bank.
  kRomExtPageCount = CHIP_ROM_EXT_SIZE_MAX / kFlashBytesPerPage,

  // The start page used by this test. Points to the start of the owner
  // partition in bank 1, otherwise known as owner partition B.
  kBank1StartPageNum = 256 + kRomExtPageCount,
};

// The `flash_word_verify()` function will need to be updated if this assertion
// fails.
static_assert(
    FLASH_CTRL_PARAM_BYTES_PER_WORD == sizeof(uint64_t),
    "This test expects the flash word to be sizeof(uint64_t) bytes long.");

static dif_flash_ctrl_state_t flash;

/**
 * Write and verify `expected_value` at flash `address`.
 *
 * This function generates a test assertion on failure.
 *
 * @param address Flash address, uint32_t aligned.
 * @param expected_value Value to write and verify.
 */
static void flash_word_write_verify(uintptr_t address,
                                    uint64_t expected_value) {
  size_t kWordSize = sizeof(uint64_t) / sizeof(uint32_t);
  CHECK_STATUS_OK(flash_ctrl_testutils_write(
      &flash, address, kUnusedDataPartitionParam, (uint32_t *)&expected_value,
      kDifFlashCtrlPartitionTypeData, kWordSize));

  uint64_t got_value;
  CHECK_STATUS_OK(flash_ctrl_testutils_read(
      &flash, address, kUnusedDataPartitionParam, (uint32_t *)&got_value,
      kDifFlashCtrlPartitionTypeData, kWordSize,
      /*delay=*/1));
  CHECK(expected_value == got_value);
}

static void flash_ctrl_write_clear_test(
    uint32_t mp_region_index,
    dif_flash_ctrl_data_region_properties_t mp_properties) {
  // Configure a memory protected region to implement the page configuration
  // set in `mp_properties`.
  CHECK_DIF_OK(dif_flash_ctrl_set_data_region_properties(
      &flash, mp_region_index, mp_properties));
  CHECK_DIF_OK(dif_flash_ctrl_set_data_region_enablement(
      &flash, mp_region_index, kDifToggleEnabled));

  uintptr_t start_addr = (uintptr_t)(mp_properties.base * kFlashBytesPerPage);
  CHECK_STATUS_OK(flash_ctrl_testutils_erase_page(
      &flash, start_addr, kUnusedDataPartitionParam,
      kDifFlashCtrlPartitionTypeData));

  const uint64_t kExpectedValues[] = {
      UINT64_MAX, UINT64_MAX - 1, 0, 0xa5a5a5a594949494, 0xaaaaaaaaaaaaaaaa,
  };

  for (size_t i = 0; i < ARRAYSIZE(kExpectedValues); ++i) {
    flash_word_write_verify(start_addr + sizeof(uint64_t) * i,
                            kExpectedValues[i]);
    flash_word_write_verify(start_addr, /*expected_value=*/0);
  }
}

bool test_main(void) {
  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash, mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));

  // The ROM_EXT configures the default region access. We can't modify the
  // values after configured.
  if (kBootStage != kBootStageOwner) {
    CHECK_STATUS_OK(flash_ctrl_testutils_default_region_access(
        &flash, /*rd_en=*/true, /*prog_en=*/true, /*erase_en=*/true,
        /*scramble_en=*/false, /*ecc_en=*/false, /*high_endurance_en=*/false));
  }

  LOG_INFO("ECC enabled with high endurance disabled.");
  flash_ctrl_write_clear_test(/*mp_region_index=*/0,
                              (dif_flash_ctrl_data_region_properties_t){
                                  .base = kBank1StartPageNum,
                                  .size = 1,
                                  .properties = {
                                      .rd_en = kMultiBitBool4True,
                                      .prog_en = kMultiBitBool4True,
                                      .erase_en = kMultiBitBool4True,
                                      .scramble_en = kMultiBitBool4False,
                                      .ecc_en = kMultiBitBool4True,
                                      .high_endurance_en = kMultiBitBool4False,
                                  }});

  LOG_INFO("ECC enabled with high endurance enabled.");
  flash_ctrl_write_clear_test(/*mp_region_index=*/1,
                              (dif_flash_ctrl_data_region_properties_t){
                                  .base = kBank1StartPageNum + 1,
                                  .size = 1,
                                  .properties = {
                                      .rd_en = kMultiBitBool4True,
                                      .prog_en = kMultiBitBool4True,
                                      .erase_en = kMultiBitBool4True,
                                      .scramble_en = kMultiBitBool4False,
                                      .ecc_en = kMultiBitBool4True,
                                      .high_endurance_en = kMultiBitBool4True,
                                  }});

  return true;
}
