// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/base/stdasm.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/sram_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "rstmgr_regs.h"     // Generated.
#include "sram_ctrl_regs.h"  // Generated.

#define BACKDOOR_TEST_WORDS 16
#define BACKDOOR_TEST_BYTES BACKDOOR_TEST_WORDS * sizeof(uint32_t)

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

static_assert(BACKDOOR_TEST_WORDS == 16,
              "BACKDOOR_TEST_WORDS changed, so "
              "ECC_ERRORS_FALSE_POSITIVE_FLOOR_LIMIT should be "
              "computed again");
/**
 * The offset into the main SRAM where we will backdoor write data.
 * This offset only needs to be after the location of
 * "sram_ctrl_main_scramble_buffer" as all other data in the SRAM
 * will have been scrambled at this point. Using the midpoint
 * of the SRAM.
 */
#define BACKDOOR_MAIN_RAM_OFFSET \
  (TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_SIZE_BYTES / 8)

/**
 * The offset in the retention SRAM where we will copy the data
 * read from the main SRAM that was written by the backdoor. This
 * location needs to be after SRAM_CTRL_TESTUTILS_DATA_NUM_WORDS which
 * is the end of where the scrambled data is located.
 */
#define RET_RAM_COPY_OFFSET SRAM_CTRL_TESTUTILS_DATA_NUM_WORDS

/**
 * The offset in the retention SRAM to store the ECC error count.
 */
#define ECC_ERROR_COUNT_OFFSET \
  ((RET_RAM_COPY_OFFSET * sizeof(uint32_t)) + BACKDOOR_TEST_BYTES)

OTTF_DEFINE_TEST_CONFIG();

static dif_sram_ctrl_t sram_ctrl;

/**
 * MAIN SRAM scrambling test buffer.
 *
 * This buffer is initialized with a known pattern, which will be overwritten
 * with a pseudo-random data as the result of MAIN SRAM scrambling.
 */
static volatile uint32_t
    sram_ctrl_main_scramble_buffer[SRAM_CTRL_TESTUTILS_DATA_NUM_WORDS];

/**
 * Test pattern to be written and read from SRAM.
 */
static const uint32_t kRamTestPattern1[] = {
    0xA5A5A5A5,
    0xA23DE94C,
    0xD82A4FB0,
    0xE3CA4D62,
};

/**
 * Test pattern to be written and read from SRAM.
 */
static const uint32_t kRamTestPattern2[] = {
    0x5A5A5A5A,
    0x3CFB4A77,
    0x304C6528,
    0xFAEFD5CC,
};

/**
 * Expected data for the backdoor write test, to be written from the testbench.
 */
static const uint8_t kBackdoorExpectedBytes[BACKDOOR_TEST_BYTES];

/**
 * SRAM backdoor offset address.
 */
static const uint32_t kMainRamBackdoorOffset =
    TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_BASE_ADDR +
    (BACKDOOR_MAIN_RAM_OFFSET * sizeof(uint32_t));

/**
 * The address in the retention SRAM where the backdoor written
 * data will be copied to be checked after reset.
 */
static const uint32_t kRetRamBackdoorOffset =
    TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR +
    (RET_RAM_COPY_OFFSET * sizeof(uint32_t));

/**
 * Retention SRAM start address (inclusive).
 */
static const uintptr_t kRetSramAddr =
    TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR;

/**
 * Performs scrambling, saves the test relevant data and resets the system.
 *
 * This code is written in assembly because MAIN SRAM addresses will be
 * scrambled, which has a similar effect to overwriting with pseudo-random
 * data. This will thrash the SRAM (including .bss, .data segments and the
 * stack), effectively rendering the C runtime environment invalid.
 *
 * This function saves contents of the `sram_ctrl_main_scramble_buffer` and
 * the data written from the testbench in the RETENTION SRAM, which is
 * kept intact across the system reboot.
 */
static noreturn void main_sram_scramble(void) {
  asm volatile(
      // Request the new scrambling key for MAIN SRAM.
      "li t0, 0x1                                                   \n"
      "sw t0, %[kSramCtrlOffset](%[kSramCtrlRegsBase])              \n"

      // Busy loop - waiting for scrambling to finish.
      ".L_scrambling_busy_loop:                                     \n"
      "  lw t0, %[kSramCtrlStatusOffset](%[kSramCtrlRegsBase])      \n"
      "  andi t0, t0, %[kSramCtrlKeyScrDone]                        \n"
      "  beqz t0, .L_scrambling_busy_loop                           \n"

      // Copy the buffer contents to the retention SRAM.
      ".L_buffer_copy_loop:                                         \n"
      "  lw t0, 0(%[kCopyFromAddr])                                 \n"
      "  sw t0, 0(%[kCopyToAddr])                                   \n"
      "  addi %[kCopyFromAddr], %[kCopyFromAddr], 4                 \n"
      "  addi %[kCopyToAddr], %[kCopyToAddr], 4                     \n"
      "  blt %[kCopyToAddr], %[kCopyToEndAddr], .L_buffer_copy_loop \n"

      // Copy the backdoor written contents to the retention SRAM.
      ".L_offset_copy_loop:                                         \n"
      "  lw t0, 0(%[kOffsetCopyFromAddr])                           \n"
      "  sw t0, 0(%[kOffsetCopyToAddr])                             \n"
      "  addi %[kOffsetCopyFromAddr], %[kOffsetCopyFromAddr], 4     \n"
      "  addi %[kOffsetCopyToAddr], %[kOffsetCopyToAddr], 4         \n"
      "  blt %[kOffsetCopyToAddr], %[kOffsetCopyToEndAddr], "
      ".L_offset_copy_loop \n"

      // Trigger the software system reset via the Reset Manager.
      "li t0, %[kMultiBitTrue]                                      \n"
      "sw t0, %[kRstMgrResetReq](%[kRstMgrRegsBase])                \n"

      // Satisfy the `noreturn` promise to the compiler.
      ".L_infinite_loop:                                            \n"
      "  wfi                                                        \n"
      "  j .L_infinite_loop"
      :
      : [kMultiBitTrue] "I"(kMultiBitBool4True),

        [kSramCtrlRegsBase] "r"(TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR),
        [kSramCtrlOffset] "I"(SRAM_CTRL_CTRL_REG_OFFSET),
        [kSramCtrlStatusOffset] "I"(SRAM_CTRL_STATUS_REG_OFFSET),
        // TODO(lowRISC/opentitan#8546): reading from scrambled but not
        // initialized SRAM may trigger ECC errors.
        [kSramCtrlKeyScrDone] "I"(0x1 << SRAM_CTRL_STATUS_SCR_KEY_VALID_BIT),

        [kRstMgrRegsBase] "r"(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR),
        [kRstMgrResetReq] "I"(RSTMGR_RESET_REQ_REG_OFFSET),

        [kCopyFromAddr] "r"(sram_ctrl_main_scramble_buffer),
        [kCopyToAddr] "r"(TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR),
        [kCopyToEndAddr] "r"(TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR +
                             (SRAM_CTRL_TESTUTILS_DATA_NUM_WORDS * 4)),

        [kOffsetCopyFromAddr] "r"(kMainRamBackdoorOffset),
        [kOffsetCopyToAddr] "r"(kRetRamBackdoorOffset),
        [kOffsetCopyToEndAddr] "r"(kRetRamBackdoorOffset +
                                   (BACKDOOR_TEST_WORDS * 4))

      : "t0");

  OT_UNREACHABLE();
}

/**
 * Checks whether the system reset was requested by the software.
 */
static bool reentry_after_system_reset(void) {
  dif_rstmgr_t rstmgr;
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));
  return rstmgr_testutils_reset_info_any(&rstmgr, kDifRstmgrResetInfoSw);
}

/**
 * Prepares the MAIN SRAM and the RETENTION SRAM buffers.
 *
 * Makes sure that both buffers can be read and written to, and are initialized
 * to the opposite patterns.
 */
static void prepare_for_scrambling(void) {
  // Make sure we can write and read to the retention SRAM.
  sram_ctrl_testutils_write(
      kRetSramAddr,
      (sram_ctrl_testutils_data_t){.words = kRamTestPattern2,
                                   .len = ARRAYSIZE(kRamTestPattern2)});
  sram_ctrl_testutils_write(
      kRetSramAddr,
      (sram_ctrl_testutils_data_t){.words = kRamTestPattern1,
                                   .len = ARRAYSIZE(kRamTestPattern1)});

  CHECK_ARRAYS_EQ((uint32_t *)kRetSramAddr, kRamTestPattern1,
                  ARRAYSIZE(kRamTestPattern1));

  // Make sure we can write and read the buffer in MAIN SRAM.
  sram_ctrl_testutils_write(
      (uintptr_t)&sram_ctrl_main_scramble_buffer,
      (sram_ctrl_testutils_data_t){.words = kRamTestPattern1,
                                   .len = ARRAYSIZE(kRamTestPattern1)});

  sram_ctrl_testutils_write(
      (uintptr_t)&sram_ctrl_main_scramble_buffer,
      (sram_ctrl_testutils_data_t){.words = kRamTestPattern2,
                                   .len = ARRAYSIZE(kRamTestPattern2)});

  CHECK_ARRAYS_EQ(sram_ctrl_main_scramble_buffer, kRamTestPattern2,
                  ARRAYSIZE(kRamTestPattern2));
}

/**
 * Override internal IRQ interrupt service routine to count
 * the number of integrity exceptions.
 */
void ottf_internal_isr(void) {
  mmio_region_t mem_region = mmio_region_from_addr(kRetSramAddr);
  uint32_t exception_count =
      mmio_region_read32(mem_region, ECC_ERROR_COUNT_OFFSET);
  mmio_region_write32(mem_region, ECC_ERROR_COUNT_OFFSET, ++exception_count);
}

/**
 * Executes the MAIN SRAM scrambling test.
 *
 * This test is re-entrant. On the first pass the test triggers MAIN SRAM
 * scrambling, saves the relevant test data in RETENTION SRAM, and triggers the
 * system reset. On the second pass, it compares the saved test data against
 * the expected pattern.
 */
bool test_main(void) {
  CHECK_DIF_OK(dif_sram_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR),
      &sram_ctrl));

  if (reentry_after_system_reset()) {
    // Second boot, check the values.
    CHECK_ARRAYS_NE((uint32_t *)kRetSramAddr, kRamTestPattern1,
                    ARRAYSIZE(kRamTestPattern1));

    CHECK_ARRAYS_NE((uint32_t *)kRetSramAddr, kRamTestPattern2,
                    ARRAYSIZE(kRamTestPattern2));

    // Statistically there is always a chance that after changing the scrambling
    // key the ECC bits are correct and no IRQ is triggered. So we tolerate a
    // minimum of false positives.
    uint32_t ecc_errors = mmio_region_read32(
        mmio_region_from_addr(kRetSramAddr), ECC_ERROR_COUNT_OFFSET);
    uint32_t false_positives = SRAM_CTRL_TESTUTILS_DATA_NUM_WORDS - ecc_errors;

    if (false_positives > 0) {
      if (false_positives > ECC_ERRORS_FALSE_POSITIVE_FLOOR_LIMIT) {
        LOG_ERROR("Failed as it didn't generate enough ECC errors(%d/%d)",
                  false_positives, ECC_ERRORS_FALSE_POSITIVE_FLOOR_LIMIT);
        return false;
      }
      LOG_INFO("Passing with a remark, %d words didn't generate ECC errors",
               false_positives);
    }

    sram_ctrl_testutils_check_backdoor_write(kRetSramAddr, BACKDOOR_TEST_WORDS,
                                             RET_RAM_COPY_OFFSET,
                                             kBackdoorExpectedBytes);
  } else {
    // First boot, prepare the test.
    mmio_region_write32(mmio_region_from_addr(kRetSramAddr),
                        ECC_ERROR_COUNT_OFFSET, 0);

    prepare_for_scrambling();
    main_sram_scramble();
  }

  return true;
}
