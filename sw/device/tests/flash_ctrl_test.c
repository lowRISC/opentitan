// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/flash_ctrl.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_main.h"

#define CHECK_ARRAYS_EQ(xs, ys, len) \
  do {                               \
    uint32_t *xs_ = (xs);            \
    uint32_t *ys_ = (ys);            \
    size_t len_ = (len);             \
    for (int i = 0; i < len_; ++i) { \
      CHECK(xs_[i] == ys_[i]);       \
    }                                \
  } while (false)

#define CHECK_EQZ(x) CHECK((x) == 0)
#define CHECK_NEZ(x) CHECK((x) != 0)

#define FLASH_WORDS_PER_PAGE flash_get_words_per_page()
#define FLASH_WORD_SZ flash_get_word_size()
#define FLASH_PAGE_SZ flash_get_page_size()
#define FLASH_PAGES_PER_BANK flash_get_pages_per_bank()
#define FLASH_BANK_SZ flash_get_bank_size()

/*
 * Basic test of page erase / program / read functions
 * Tests pages from both the data and info partitions
 */
static void test_basic_io(void) {
  // setup default access for data partition
  flash_default_region_access(/*rd_en=*/true, /*prog_en=*/true,
                              /*erase_en=*/true);

  // info partition has no default access, specifically setup a region
  mp_region_t info_region = {.num = 0x0,
                             .base = FLASH_PAGES_PER_BANK,
                             .size = 0x1,
                             .part = kInfoPartition,
                             .rd_en = true,
                             .prog_en = true,
                             .erase_en = true,
                             .scramble_en = true};
  flash_cfg_region(&info_region);

  // also setup data region to enable scrambling
  mp_region_t data_region = {.num = 0x0,
                             .base = FLASH_PAGES_PER_BANK,
                             .size = 0x1,
                             .part = kDataPartition,
                             .rd_en = true,
                             .prog_en = true,
                             .erase_en = true,
                             .scramble_en = true};
  flash_cfg_region(&data_region);

  uintptr_t flash_bank_1_addr = FLASH_MEM_BASE_ADDR + FLASH_BANK_SZ;
  mmio_region_t flash_bank_1 = mmio_region_from_addr(flash_bank_1_addr);

  // Test erasing flash data partition; this should turn the whole bank to all
  // ones.
  CHECK_EQZ(flash_page_erase(flash_bank_1_addr, kDataPartition));
  for (int i = 0; i < FLASH_WORDS_PER_PAGE; ++i) {
    CHECK_EQZ(~mmio_region_read32(flash_bank_1, i * sizeof(uint32_t)));
  }

  // Erasing flash info partition; this should turn the whole bank to all ones.
  CHECK_EQZ(flash_page_erase(flash_bank_1_addr, kInfoPartition));

  // Prepare an entire page of non-trivial data to program
  // into flash.
  uint32_t input_page[FLASH_WORDS_PER_PAGE];
  uint32_t output_page[FLASH_WORDS_PER_PAGE];
  memset(input_page, 0xa5, FLASH_WORDS_PER_PAGE * sizeof(uint32_t));
  for (int i = 0; i < FLASH_WORDS_PER_PAGE; i += 2) {
    input_page[i] ^= 0xffffffff;
  }

  // Attempt to live-program an entire page, where the overall
  // payload is much larger than the internal flash FIFO.
  CHECK_EQZ(flash_page_erase(flash_bank_1_addr, kDataPartition));
  CHECK_EQZ(flash_write(flash_bank_1_addr, kDataPartition, input_page,
                        FLASH_WORDS_PER_PAGE));
  CHECK_EQZ(flash_read(flash_bank_1_addr, kDataPartition, FLASH_WORDS_PER_PAGE,
                       output_page));
  CHECK_ARRAYS_EQ(output_page, input_page, FLASH_WORDS_PER_PAGE);

  // Check from host side also
  for (int i = 0; i < FLASH_WORDS_PER_PAGE; i++) {
    output_page[i] = mmio_region_read32(flash_bank_1, i * sizeof(uint32_t));
  }
  CHECK_ARRAYS_EQ(output_page, input_page, FLASH_WORDS_PER_PAGE);

  // Similar check for info page
  CHECK_EQZ(flash_page_erase(flash_bank_1_addr, kInfoPartition));
  CHECK_EQZ(flash_write(flash_bank_1_addr, kInfoPartition, input_page,
                        FLASH_WORDS_PER_PAGE));
  CHECK_EQZ(flash_read(flash_bank_1_addr, kInfoPartition, FLASH_WORDS_PER_PAGE,
                       output_page));
  CHECK_ARRAYS_EQ(output_page, input_page, FLASH_WORDS_PER_PAGE);

  uintptr_t flash_bank_0_last_page_addr = flash_bank_1_addr - FLASH_PAGE_SZ;
  mmio_region_t flash_bank_0_last_page =
      mmio_region_from_addr(flash_bank_0_last_page_addr);
  CHECK_EQZ(flash_page_erase(flash_bank_0_last_page_addr, kDataPartition));
  for (int i = 0; i < FLASH_WORDS_PER_PAGE; ++i) {
    CHECK_EQZ(
        ~mmio_region_read32(flash_bank_0_last_page, i * sizeof(uint32_t)));
  }

  CHECK_EQZ(flash_write(flash_bank_0_last_page_addr, kDataPartition, input_page,
                        FLASH_WORDS_PER_PAGE));
  CHECK_EQZ(flash_read(flash_bank_0_last_page_addr, kDataPartition,
                       FLASH_WORDS_PER_PAGE, output_page));

  CHECK_ARRAYS_EQ(output_page, input_page, FLASH_WORDS_PER_PAGE);
}

static void test_memory_protection(void) {
  flash_default_region_access(/*rd_en=*/true, /*prog_en=*/true,
                              /*erase_en=*/true);

  // A memory protection region representing the first page of the second bank.
  mp_region_t protection_region = {.num = 0x0,
                                   .base = FLASH_PAGES_PER_BANK,
                                   .size = 0x1,
                                   .part = kDataPartition,
                                   .rd_en = true,
                                   .prog_en = true,
                                   .erase_en = true,
                                   .scramble_en = false};

  uintptr_t ok_region_start =
      FLASH_MEM_BASE_ADDR + (protection_region.base * FLASH_PAGE_SZ);
  uintptr_t ok_region_end =
      ok_region_start + (protection_region.size * FLASH_PAGE_SZ);
  mmio_region_t ok_region = mmio_region_from_addr(ok_region_start);

  uintptr_t bad_region_start = ok_region_end;

  // Erase good and bad regions.
  CHECK_EQZ(flash_page_erase(ok_region_start, kDataPartition));
  CHECK_EQZ(flash_page_erase(bad_region_start, kDataPartition));

  // Turn off flash access by default.
  flash_default_region_access(/*rd_en=*/false, /*prog_en=*/false,
                              /*erase_en=*/false);
  flash_cfg_region(&protection_region);

  // Attempt to perform a write.
  uintptr_t region_boundary_start = bad_region_start - (FLASH_WORD_SZ * 2);
  mmio_region_t region_boundary = mmio_region_from_addr(region_boundary_start);

  // Place half the words in the good region and half in the bad
  uint32_t words[(FLASH_WORD_SZ * 2 * 2) / sizeof(uint32_t)];
  memset(words, 0xa5, ARRAYSIZE(words) * sizeof(uint32_t));
  for (int i = 0; i < ARRAYSIZE(words); ++i) {
    words[i] += i;
  }

  // Perform a partial write.
  CHECK_NEZ(flash_write(region_boundary_start, kDataPartition, words,
                        ARRAYSIZE(words)));
  // Words in the good region should still match, while words in the bad
  // region should be all-ones, since we erased
  for (int i = 0; i < ARRAYSIZE(words); ++i) {
    uint32_t expected = 0xffffffff;
    if (i < ARRAYSIZE(words) / 2) {
      expected = words[i];
    }
    CHECK(mmio_region_read32(region_boundary, i * sizeof(uint32_t)) ==
          expected);
  }

  // Attempt to erase bad page, which should fail.
  CHECK_NEZ(flash_page_erase(bad_region_start, kDataPartition));

  // Attempt to erase the good page, which should succeed.
  CHECK_EQZ(flash_page_erase(ok_region_start, kDataPartition));
  for (int i = 0; i < FLASH_WORDS_PER_PAGE; i++) {
    CHECK_EQZ(~mmio_region_read32(ok_region, i * sizeof(uint32_t)));
  }
}

const test_config_t kTestConfig;

bool test_main(void) {
  flash_init_block();

  LOG_INFO("flash test!");

  flash_cfg_bank_erase(FLASH_BANK_0, /*erase_en=*/true);
  flash_cfg_bank_erase(FLASH_BANK_1, /*erase_en=*/true);

  test_basic_io();
  test_memory_protection();

  flash_cfg_bank_erase(FLASH_BANK_0, /*erase_en=*/false);
  flash_cfg_bank_erase(FLASH_BANK_1, /*erase_en=*/false);

  return true;
}
