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
#include "sw/device/lib/testing/test_framework/ottf.h"
#include "sw/device/lib/testing/test_framework/test_status.h"

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

const test_config_t kTestConfig;

static dif_sram_ctrl_t sram_ctrl;
static dif_rstmgr_t rstmgr;

/**
 * Retention SRAM start address (inclusive).
 */
static const uintptr_t kRetSramStartAddr =
    TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR;

/**
 * First test pattern to be written and read from SRAM.
 */
static const sram_ctrl_testutils_data_t kRamTestPattern1 = {
    .words =
        {
            0xA5A5A5A5,
            0xA5A5A5A5,
            0xA5A5A5A5,
            0xA5A5A5A5,
        },
};

/**
 * Second test pattern to be written and read from SRAM.
 */
static const sram_ctrl_testutils_data_t kRamTestPattern2 = {
    .words =
        {
            0x5A5A5A5A,
            0x5A5A5A5A,
            0x5A5A5A5A,
            0x5A5A5A5A,
        },
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
  sram_ctrl_testutils_write(kRetSramStartAddr, &kRamTestPattern1);
  CHECK(sram_ctrl_testutils_read_check_eq(kRetSramStartAddr, &kRamTestPattern1),
        "Read-Write first pattern failed");

  // Write second pattern to the start of SRAM, and read it out.
  sram_ctrl_testutils_write(kRetSramStartAddr, &kRamTestPattern2);
  CHECK(sram_ctrl_testutils_read_check_eq(kRetSramStartAddr, &kRamTestPattern2),
        "Read-Write second pattern failed");
}

/**
 * Tests RAM Scrambling.
 *
 * This test first writes a pattern to the start and the end of RAM. It then
 * requests a new scrambling key via dif_sram_ctrl (which scrambles RAM
 * addresses as well as the data). Finally, it reads back the RAM addresses
 * and checks them against the original pattern. The test is successful if
 * these patterns don't match.
 */
bool test_ram_scrambling(const dif_sram_ctrl_t *sram_ctrl) {
  // Write the pattern at the start of RAM.
  sram_ctrl_testutils_write(kRetSramStartAddr, &kRamTestPattern1);

  sram_ctrl_testutils_scramble(sram_ctrl);

  // Read the first pattern at the start of RAM. It should NOT match the
  // originally written pattern.
  return sram_ctrl_testutils_read_check_neq(kRetSramStartAddr,
                                            &kRamTestPattern1);
}

bool test_main(void) {
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));
  CHECK_DIF_OK(dif_sram_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_BASE_ADDR),
      &sram_ctrl));

  sram_ctrl_testutils_wipe(&sram_ctrl);
  test_ram_write_read_pattern();

  // There is a non-zero chance that the value at the tested address by pure
  // chance will be the same. So just to be prudent, in case of the failure,
  // scrambling is tested again.
  if (!test_ram_scrambling(&sram_ctrl)) {
    LOG_WARNING("Initial retention RAM scramble test(s) failed, running again");
    CHECK(test_ram_scrambling(&sram_ctrl),
          "Retention RAM Scrambling test has failed (double-checked)");
  }

  sram_ctrl_testutils_check_backdoor_write(kRetSramStartAddr,
                                           SRAM_CTRL_BACKDOOR_TEST_WORDS,
                                           RET_OFFSET, kBackdoorExpectedBytes);

  CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));

  return true;
}
