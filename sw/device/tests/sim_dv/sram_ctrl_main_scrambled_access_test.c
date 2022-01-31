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
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/sram_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf.h"
#include "sw/device/lib/testing/test_framework/test_status.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "rstmgr_regs.h"     // Generated.
#include "sram_ctrl_regs.h"  // Generated.

#define BACKDOOR_TEST_WORDS 16
#define BACKDOOR_TEST_BYTES BACKDOOR_TEST_WORDS * sizeof(uint32_t)

/* The offset into the main SRAM where we will backdoor write data.
 * This offset only needs to be after the location of
 * "sram_ctrl_main_scramble_buffer" as all other data in the SRAM
 * will have been scrambled at this point. Using the midpoint
 * of the SRAM.
 */
#define BACKDOOR_MAIN_RAM_OFFSET \
  (TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_SIZE_BYTES / 8)

/* The offset in the retention SRAM where we will copy the data
 * read from the main SRAM that was written by the backdoor. This
 * location needs to be after SRAM_CTRL_TESTUTILS_DATA_NUM_WORDS which
 * is the end of where the scrambled data is located.
 */
#define RET_RAM_COPY_OFFSET SRAM_CTRL_TESTUTILS_DATA_NUM_WORDS

const test_config_t kTestConfig;

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
 * Test pattern to be written and read from SRAM.
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
  sram_ctrl_testutils_write(TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR,
                            &kRamTestPattern2);
  sram_ctrl_testutils_write(TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR,
                            &kRamTestPattern1);
  CHECK(sram_ctrl_testutils_read_check_eq(
      TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR, &kRamTestPattern1));

  // Make sure we can write and read the buffer in MAIN SRAM.
  sram_ctrl_testutils_write((uintptr_t)&sram_ctrl_main_scramble_buffer,
                            &kRamTestPattern1);
  sram_ctrl_testutils_write((uintptr_t)&sram_ctrl_main_scramble_buffer,
                            &kRamTestPattern2);
  CHECK(sram_ctrl_testutils_read_check_eq(
      (uintptr_t)&sram_ctrl_main_scramble_buffer, &kRamTestPattern2));
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
    CHECK(sram_ctrl_testutils_read_check_neq(
        TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR, &kRamTestPattern1));
    CHECK(sram_ctrl_testutils_read_check_neq(
        TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR, &kRamTestPattern2));

    sram_ctrl_testutils_check_backdoor_write(
        TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR, BACKDOOR_TEST_WORDS,
        RET_RAM_COPY_OFFSET, kBackdoorExpectedBytes);
  } else {
    prepare_for_scrambling();
    main_sram_scramble();
  }

  return true;
}
