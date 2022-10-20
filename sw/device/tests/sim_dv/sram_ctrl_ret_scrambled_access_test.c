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

/**
 * Note that there are `2^32` valid code words and that each non-valid code
 * word triggers an error. Therefore, the probability that a random 39-bit
 * word triggers an error is: `(2^39 - 2^32)/ 2^39 = 127/128`. Then the
 * probability that all `BACKDOOR_TEST_WORDS` triggers an errors is
 * `(127/128)^BACKDOOR_TEST_WORDS` after re-scrambling.
 *
 * The Generic formula:
 *
 *               (w-i)
 *             127
 * Pr(i) =  -------- x (w choose i)
 *                w
 *             128
 * Where:
 *      w = The number of words tested.
 *      i = The number of words that may not generate errors.
 *      Pr(i) = Probability that i words will not generate an ECC error.
 *
 * So for i in (0..3):
 *
 * ``` Python
 * from math import comb
 * w = 16
 * t = 0
 * for i in range(4):
 *    p = ((127**(w-i))/(128**w)) * comb(w,i)
 *    t += p
 *    print(f'Pr({i}): { round(p, 4)},\tsum{{Pr(0-{i})}}: {round(t, 6)}')
 * ```
 * ```
 * Pr(0): 0.8821,   sum{Pr(0-0)}: 0.882064
 * Pr(1): 0.1111,   sum{Pr(0-1)}: 0.99319
 * Pr(2): 0.0066,   sum{Pr(0-2)}: 0.999753
 * Pr(3): 0.0002,   sum{Pr(0-3)}: 0.999994
 * ```
 * So by choosing 1 as the floor limit we will a have probability of `1 -
 * 0.99319 = 0.68%` that this test would fail randomly due to ECC errors not
 * being generated.
 */
#define ECC_ERRORS_FALSE_POSITIVE_FLOOR_LIMIT 1

static_assert(SRAM_CTRL_BACKDOOR_TEST_WORDS == 16,
              "BACKDOOR_TEST_WORDS changed, so "
              "ECC_ERRORS_FALSE_POSITIVE_FLOOR_LIMIT should be "
              "computed again");

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
  // Reading before comparing just to make sure it will always read all the
  // words and the right amount of ECC errors will be generated.
  uint32_t tmp_buffer[ARRAYSIZE(kRamTestPattern1)];
  memcpy(tmp_buffer, (const uint8_t *)kRetSramStartAddr, sizeof(tmp_buffer));
  CHECK_ARRAYS_NE(tmp_buffer, kRamTestPattern1, ARRAYSIZE(kRamTestPattern1));

  uint32_t false_positives =
      ARRAYSIZE(kRamTestPattern1) - integrity_exception_count;

  if (false_positives > 0) {
    CHECK(false_positives > ECC_ERRORS_FALSE_POSITIVE_FLOOR_LIMIT,
          "Failed as it didn't generate enough ECC errors(%d/%d)",
          false_positives, ECC_ERRORS_FALSE_POSITIVE_FLOOR_LIMIT);
    LOG_INFO("Passing with a remark, %d words didn't generate ECC errors",
             false_positives);
  }
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
