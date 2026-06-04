// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/nvm_testutils.h"

#include <string.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Maximum word count supported for the write readback buffer.
enum { kNvmMaxWordCount = 64 };

// Physical location of a logical NVM info page.
typedef struct {
  uint32_t page_id;
  uint32_t bank;
  uint32_t partition_id;
} nvm_page_phys_t;

// Mapping from logical nvm_info_page_t to physical flash parameters.
// Update this table when switching to a different NVM technology.
static const nvm_page_phys_t kPageMap[] = {
    [kNvmInfoPageFactory] = {.page_id = 0, .bank = 0, .partition_id = 0},
    [kNvmInfoPageCreatorSecret] = {.page_id = 1, .bank = 0, .partition_id = 0},
    [kNvmInfoPageOwnerSecret] = {.page_id = 2, .bank = 0, .partition_id = 0},
    [kNvmInfoPageWaferAuthSecret] = {.page_id = 3,
                                     .bank = 0,
                                     .partition_id = 0},
    [kNvmInfoPageAttestationKeySeeds] = {.page_id = 4,
                                         .bank = 0,
                                         .partition_id = 0},
};

static status_t nvm_ctrl_init(dif_flash_ctrl_state_t *flash) {
  TRY(dif_flash_ctrl_init_state(
      flash, mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
  return OK_STATUS();
}

status_t nvm_testutils_write_info_page(nvm_info_page_t page,
                                       uint32_t byte_offset,
                                       const uint32_t *data, size_t word_count,
                                       bool scramble, bool erase_before_write) {
  TRY_CHECK(page < ARRAYSIZE(kPageMap), "invalid page %d", page);
  TRY_CHECK(word_count <= kNvmMaxWordCount, "word_count %d exceeds max %d",
            word_count, kNvmMaxWordCount);
  const nvm_page_phys_t p = kPageMap[page];

  dif_flash_ctrl_state_t flash;
  TRY(nvm_ctrl_init(&flash));

  uint32_t page_base = 0;
  if (scramble) {
    TRY(flash_ctrl_testutils_info_region_scrambled_setup(
        &flash, p.page_id, p.bank, p.partition_id, &page_base));
  } else {
    TRY(flash_ctrl_testutils_info_region_setup(&flash, p.page_id, p.bank,
                                               p.partition_id, &page_base));
  }
  uint32_t address = page_base + byte_offset;

  if (erase_before_write) {
    TRY(flash_ctrl_testutils_erase_and_write_page(
        &flash, address, p.partition_id, data, kDifFlashCtrlPartitionTypeInfo,
        word_count));
    uint32_t readback[kNvmMaxWordCount];
    TRY(flash_ctrl_testutils_read(&flash, address, p.partition_id, readback,
                                  kDifFlashCtrlPartitionTypeInfo, word_count,
                                  0));
    TRY_CHECK(memcmp(data, readback, word_count * sizeof(uint32_t)) == 0,
              "NVM write readback mismatch at page %d offset %d", page,
              byte_offset);
  } else {
    TRY(flash_ctrl_testutils_write(&flash, address, p.partition_id, data,
                                   kDifFlashCtrlPartitionTypeInfo, word_count));
  }
  return OK_STATUS();
}

status_t nvm_testutils_enable_data_access(bool rd_en, bool prog_en,
                                          bool erase_en, bool scramble_en,
                                          bool ecc_en, bool high_endurance_en) {
  dif_flash_ctrl_state_t flash;
  TRY(nvm_ctrl_init(&flash));
  TRY(flash_ctrl_testutils_default_region_access(&flash, rd_en, prog_en,
                                                 erase_en, scramble_en, ecc_en,
                                                 high_endurance_en));
  return OK_STATUS();
}

status_t nvm_testutils_info_region_setup(uint32_t page_id, uint32_t bank,
                                         uint32_t partition_id,
                                         uint32_t *offset) {
  dif_flash_ctrl_state_t flash;
  TRY(nvm_ctrl_init(&flash));
  TRY(flash_ctrl_testutils_info_region_setup(&flash, page_id, bank,
                                             partition_id, offset));
  return OK_STATUS();
}

status_t nvm_testutils_info_region_scrambled_setup(uint32_t page_id,
                                                   uint32_t bank,
                                                   uint32_t partition_id,
                                                   uint32_t *offset) {
  dif_flash_ctrl_state_t flash;
  TRY(nvm_ctrl_init(&flash));
  TRY(flash_ctrl_testutils_info_region_scrambled_setup(&flash, page_id, bank,
                                                       partition_id, offset));
  return OK_STATUS();
}

status_t nvm_testutils_read_info_page(nvm_info_page_t page,
                                      uint32_t byte_offset, uint32_t *data,
                                      size_t word_count) {
  TRY_CHECK(page < ARRAYSIZE(kPageMap), "invalid page %d", page);
  const nvm_page_phys_t p = kPageMap[page];

  dif_flash_ctrl_state_t flash;
  TRY(nvm_ctrl_init(&flash));

  uint32_t page_base = 0;
  TRY(flash_ctrl_testutils_info_region_setup(&flash, p.page_id, p.bank,
                                             p.partition_id, &page_base));

  TRY(flash_ctrl_testutils_read(&flash, page_base + byte_offset, p.partition_id,
                                data, kDifFlashCtrlPartitionTypeInfo,
                                word_count, 0));
  return OK_STATUS();
}

status_t nvm_testutils_info_region_setup_properties(
    uint32_t page_id, uint32_t bank, uint32_t partition_id,
    dif_flash_ctrl_region_properties_t props, uint32_t *offset) {
  dif_flash_ctrl_state_t flash;
  TRY(nvm_ctrl_init(&flash));
  TRY(flash_ctrl_testutils_info_region_setup_properties(
      &flash, page_id, bank, partition_id, props, offset));
  return OK_STATUS();
}

status_t nvm_testutils_set_info_page_access(uint32_t page_id, uint32_t bank,
                                            uint32_t partition_id, bool rd_en,
                                            bool prog_en, bool erase_en,
                                            bool scramble_en, bool ecc_en,
                                            bool high_endurance_en,
                                            uint32_t *offset) {
  dif_flash_ctrl_region_properties_t props = {
      .rd_en = rd_en ? kMultiBitBool4True : kMultiBitBool4False,
      .prog_en = prog_en ? kMultiBitBool4True : kMultiBitBool4False,
      .erase_en = erase_en ? kMultiBitBool4True : kMultiBitBool4False,
      .scramble_en = scramble_en ? kMultiBitBool4True : kMultiBitBool4False,
      .ecc_en = ecc_en ? kMultiBitBool4True : kMultiBitBool4False,
      .high_endurance_en =
          high_endurance_en ? kMultiBitBool4True : kMultiBitBool4False,
  };
  return nvm_testutils_info_region_setup_properties(page_id, bank, partition_id,
                                                    props, offset);
}

status_t nvm_testutils_erase_and_write_info_page(uint32_t byte_address,
                                                 uint32_t partition_id,
                                                 const uint32_t *data,
                                                 size_t word_count) {
  dif_flash_ctrl_state_t flash;
  TRY(nvm_ctrl_init(&flash));
  TRY(flash_ctrl_testutils_erase_and_write_page(
      &flash, byte_address, partition_id, data, kDifFlashCtrlPartitionTypeInfo,
      word_count));
  return OK_STATUS();
}
