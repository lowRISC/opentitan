// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/sram_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/test_main.h"
#include "sw/device/lib/testing/test_framework/test_status.h"

const test_config_t kTestConfig;

static const sram_ctrl_data_t kRamTestPattern1 = {
    .words =
        {
            0xA5A5A5A5,
            0xA5A5A5A5,
            0xA5A5A5A5,
            0xA5A5A5A5,
        },
};

static const sram_ctrl_data_t kRamTestPattern2 = {
    .words =
        {
            0x5A5A5A5A,
            0x5A5A5A5A,
            0x5A5A5A5A,
            0x5A5A5A5A,
        },
};

/**
 * Tests that the written data to RAM can be read.
 *
 * This is a pre-requisite test to check that RAM can be written and read
 * successfully. The test write-read check one pattern, and then the second,
 * which prevents a false-negative in case of the value of the memory address
 * under test is already initialised to one of the patterns.
 */
static void test_ram_write_read_pattern(const sram_ctrl_t *sram) {
  // Write first pattern to the start and the end of RAM.
  sram_ctrl_write_to_ram(sram, &kRamTestPattern1);
  CHECK(sram_ctrl_read_from_ram_eq(sram, &kRamTestPattern1),
        "Read-Write first pattern failed");

  // Write second pattern to the start and the end of RAM.
  sram_ctrl_write_to_ram(sram, &kRamTestPattern2);
  CHECK(sram_ctrl_read_from_ram_eq(sram, &kRamTestPattern2),
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
bool test_ram_scrambling(const sram_ctrl_t *sram) {
  // Write the pattern at the beginning and the end of RAM.
  sram_ctrl_write_to_ram(sram, &kRamTestPattern1);

  sram_ctrl_scramble(sram);

  // Read the first pattern at the beginning and the end of RAM.
  // It should not match the originally written pattern.
  return sram_ctrl_read_from_ram_neq(sram, &kRamTestPattern1);
}

bool test_main(void) {
  sram_ctrl_t sram = sram_ctrl_ret_init();

  test_ram_write_read_pattern(&sram);

  // There is a non-zero chance that the value at the tested address by pure
  // chance will be the same. So just to be prudent, in case of the failure,
  // scrambling is tested again.
  if (!test_ram_scrambling(&sram)) {
    LOG_WARNING("Initial retention RAM scramble test(s) failed, running again");
    CHECK(test_ram_scrambling(&sram),
          "Retention RAM Scrambling test has failed (double-checked)");
  }

  return true;
}
