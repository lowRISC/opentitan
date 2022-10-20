// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/sram_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/status.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define SRAM_CTRL_BACKDOOR_TEST_WORDS 16
#define SRAM_CTRL_BACKDOOR_TEST_BYTES \
  SRAM_CTRL_BACKDOOR_TEST_WORDS * sizeof(uint32_t)

/* The offset into the retention SRAM where we will backdoor write data.
 * This can be anywhere except at the base address which is
 * already used in the test for the scramble check.
 * Using the midpoint of the SRAM.
 */
#define RET_OFFSET (TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_SIZE_BYTES / 8)

OTTF_DEFINE_TEST_CONFIG();

static dif_sram_ctrl_t sram_ctrl;
static dif_rstmgr_t rstmgr;

static volatile uint32_t integrity_exception_count;

/**
 * Retention SRAM start address (inclusive).
 */
static const uintptr_t kRetSramStartAddr =
    TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR;

/**
 * First test pattern to be written and read from SRAM.
 */
static const uint32_t kRamTestPattern1[] = {
    0xA5A5A5A5,
    0xA5A5A5A5,
    0xA5A5A5A5,
    0xA5A5A5A5,
};

/**
 * Second test pattern to be written and read from SRAM.
 */
static const uint32_t kRamTestPattern2[] = {
    0x5A5A5A5A,
    0x5A5A5A5A,
    0x5A5A5A5A,
    0x5A5A5A5A,
};

/** Expected data for the backdoor write test, to be written from the testbench.
 */
static const uint8_t kBackdoorExpectedBytes[SRAM_CTRL_BACKDOOR_TEST_BYTES];

/**
 * Tests that the written data to RAM can be read.
 *
 * This is a pre-requisite test to check that RAM can be written and read
 * successfully. The test write-read check one pattern, and then the second,
 * which prevents a false-negative in case of the value of the memory address
 * under test is already initialised to one of the patterns.
 */
static void test_ram_write_read_pattern(void) {
  // Write first pattern to the start of SRAM, and read it out.
  sram_ctrl_testutils_write(
      kRetSramStartAddr,
      (sram_ctrl_testutils_data_t){.words = kRamTestPattern1,
                                   .len = ARRAYSIZE(kRamTestPattern1)});

  CHECK_ARRAYS_EQ((uint32_t *)kRetSramStartAddr, kRamTestPattern1,
                  ARRAYSIZE(kRamTestPattern1),
                  "Read-Write first pattern failed");

  // Write second pattern to the start of SRAM, and read it out.
  sram_ctrl_testutils_write(
      kRetSramStartAddr,
      (sram_ctrl_testutils_data_t){.words = kRamTestPattern2,
                                   .len = ARRAYSIZE(kRamTestPattern2)});

  CHECK_ARRAYS_EQ((uint32_t *)kRetSramStartAddr, kRamTestPattern2,
                  ARRAYSIZE(kRamTestPattern2),
                  "Read-Write second pattern failed");
}

/**
 * Tests RAM Scrambling.
 *
 * This test first writes a pattern to the start and the end of RAM. It then
 * requests a new scrambling key via dif_sram_ctrl (which scrambles RAM
 * addresses as well as the data). Finally, it reads back the RAM addresses
 * and checks them against the original pattern. The scrambled data will cause
 * an ECC error when read back from SRAM and trigger an internal IRQ.
 * The ISR for this IRQ will count the number of exceptions. The test is
 * successful if this count is as expected and the read data mismatches.
 */
static void test_ram_scrambling(const dif_sram_ctrl_t *sram_ctrl) {
  // Write the pattern at the start of RAM.
  sram_ctrl_testutils_write(
      kRetSramStartAddr,
      (sram_ctrl_testutils_data_t){.words = kRamTestPattern1,
                                   .len = ARRAYSIZE(kRamTestPattern1)});

  sram_ctrl_testutils_scramble(sram_ctrl);
  mmio_region_t region = mmio_region_from_addr(kRetSramStartAddr);
  for (int i = 0; i < ARRAYSIZE(kRamTestPattern1); ++i) {
    uint32_t read_data = mmio_region_read32(region, sizeof(uint32_t) * i);
    CHECK(read_data != kRamTestPattern1[i]);
  }
  CHECK(integrity_exception_count == SRAM_CTRL_TESTUTILS_DATA_NUM_WORDS,
        "Scramble read exception count differs from expected.");
}

/**
 * Override internal IRQ interrupt service routine to count
 * the number of integrity exceptions.
 */
void ottf_internal_isr(void) { ++integrity_exception_count; }

bool test_main(void) {
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));
  CHECK_DIF_OK(dif_sram_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_BASE_ADDR),
      &sram_ctrl));

  sram_ctrl_testutils_wipe(&sram_ctrl);
  test_ram_write_read_pattern();

  integrity_exception_count = 0;
  test_ram_scrambling(&sram_ctrl);

  sram_ctrl_testutils_check_backdoor_write(kRetSramStartAddr,
                                           SRAM_CTRL_BACKDOOR_TEST_WORDS,
                                           RET_OFFSET, kBackdoorExpectedBytes);

  CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));

  return true;
}
