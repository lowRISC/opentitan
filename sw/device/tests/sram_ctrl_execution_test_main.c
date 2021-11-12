// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/dif/dif_sram_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/lc_ctrl_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/sram_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/test_main.h"
#include "sw/device/lib/testing/test_framework/test_status.h"

const test_config_t kTestConfig;

static volatile const uint32_t kExecParam1 = 2;
static volatile const uint32_t kExecParam2 = 3;

/**
 * Main SRAM start and end addresses (inclusive).
 */
static const uint32_t kRamStartAddr = TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_BASE_ADDR;
static const uint32_t kRamEndAddr = TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_BASE_ADDR +
                                    TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_SIZE_BYTES -
                                    1;

/**
 * OTP HW partition relative IFETCH offset in bytes.
 *
 * x = OTP_CTRL_PARAM_EN_SRAM_IFETCH_OFFSET (1728)
 * y = OTP_CTRL_PARAM_HW_CFG_OFFSET (1664)
 * IFETCH_OFFSET = (x - y) / 8 = 8
 */
static const uint32_t kOtpIfetchHwRelativeOffset = 8;

/**
 * Buffer to hold instructions to be executed.
 *
 * Because this is the Main SRAM, we let the compiler allocate the buffer
 * instead of using the hard-coded locations from the `sram_ctrl_testutil.c`,
 * in order to prevent clobbering the data used by the program.
 *
 * This can be thought of as the implementation for the `ram_exec_function_t`.
 *
 * NOTE: We explicitly specify the `.data` section, otherwise due to the
 *       `const` qualifier buffer would end up in flash. The implicit
 *       alternative would be to drop the `const` qualifier, making the buffer
 *       go into the `.data` section.
 */
__attribute__((section(
    ".data"))) static volatile const uint32_t execution_test_instructions[2] = {
    /*
     *   Abstract representation: add rd, rs1, rs2
     *   +-----------+-------+-------+-------+------+-----------+
     *   |  0000000  |  rs2  |  rs1  |  000  |  rd  |  0110011  |
     *   +-----------+-------+-------+-------+------+-----------+
     *   31        25 24   20 19   15 14   12 11   7 6          0
     *
     *   Custom representation: add a0, a1, a0
     *   +-----------+---------+---------+-------+--------+-----------+
     *   |  0000000  |  01010  |  01011  |  000  | 01010  |  0110011  |
     *   +-----------+---------+---------+-------+--------+-----------+
     *   31        25 24     20 19     15 14   12 11     7 6          0
     */
    0x00A58533,
    /*
     *   Abstract representation: ret == jalr rd, offset(rs1)
     *   +----------------+-------+-------+------+-----------+
     *   |  000000000000  |  rs1  |  000  |  rd  |  1100111  |
     *   +----------------+-------+-------+------+-----------+
     *   31             20 19   15 14   12 11   7 6          0
     *
     *   Custom representation: jalr zero, 0(ra)
     *   +----------------+---------+-------+---------+-----------+
     *   |  000000000000  |  00001  |  000  |  00000  |  1100111  |
     *   +----------------+---------+-------+---------+-----------+
     *   31             20 19     15 14   12 11      7 6          0
     */
    0x00008067,
};

/**
 * Adds the first parameter to the second parameter and returns the result.
 *
 * Maps to the `execution_test_instructions` buffer as the function body.
 */
typedef uint32_t (*ram_exec_function_t)(volatile uint32_t, volatile uint32_t);

static bool otp_ifetch_enabled(void) {
  dif_otp_ctrl_t otp;
  CHECK_DIF_OK(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp));

  dif_otp_ctrl_config_t config = {
      .check_timeout = 100000,
      .integrity_period_mask = 0x3ffff,
      .consistency_period_mask = 0x3ffffff,
  };
  CHECK_DIF_OK(dif_otp_ctrl_configure(&otp, config));

  CHECK_DIF_OK(dif_otp_ctrl_dai_read_start(&otp, kDifOtpCtrlPartitionHwCfg,
                                           kOtpIfetchHwRelativeOffset));

  otp_ctrl_testutils_wait_for_dai(&otp);

  uint32_t value;
  CHECK_DIF_OK(dif_otp_ctrl_dai_read32_end(&otp, &value));

  // OTP stores IFETCH state in a single bit (enabled/disabled).
  return bitfield_bit32_read(value, 0);
}

/**
 * Performs SRAM execution test.
 *
 * `ram_exec_function_t` is "mapped" onto the `execution_test_instructions`
 * buffer that holds hand-crafted machine instructions. Effectively, this
 * buffer becomes the function body.
 *
 * According to the calling convention the parameters will be passed in the
 * a0 and a1 registers, with a0 also treated as the return value register.
 */
static void sram_execution_test(void) {
  // Map the function pointer onto the instruction buffer.
  ram_exec_function_t func = (ram_exec_function_t)execution_test_instructions;

  uintptr_t func_address = (uintptr_t)func;
  CHECK(func_address >= kRamStartAddr && func_address <= kRamEndAddr,
        "Test code resides outside of the Main SRAM: function address = %x",
        func_address);

  uint32_t expected_result = kExecParam1 + kExecParam2;
  uint32_t result = func(kExecParam1, kExecParam2);
  CHECK(result == expected_result,
        "SRAM Execution expected %d + %d = %d, got %d", kExecParam1,
        kExecParam2, expected_result, result);
}

/**
 * Performs the tests.
 *
 * When chip is in one of the lifecycle states where debug functions are
 * enabled, execution from SRAM is enabled if the EN_SRAM_IFETCH
 * (OTP) is disabled. When EN_SRAM_IFETCH (OTP) is enabled, EXEC CSR
 * determines whether the execution from SRAM is enabled.
 */
bool test_main(void) {
  sram_ctrl_t sram = sram_ctrl_main_init();
  dif_lc_ctrl_t lc;
  CHECK_DIF_OK(dif_lc_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_BASE_ADDR), &lc));

  if (otp_ifetch_enabled()) {
    dif_toggle_t state;
    CHECK_DIF_OK(dif_sram_ctrl_exec_get_enabled(&sram.dif, &state));
    if (state == kDifToggleDisabled) {
      bool locked;
      CHECK_DIF_OK(
          dif_sram_ctrl_is_locked(&sram.dif, kDifSramCtrlLockExec, &locked));
      CHECK(!locked,
            "Execution is disabled and locked, cannot perform the test");
      CHECK_DIF_OK(
          dif_sram_ctrl_exec_set_enabled(&sram.dif, kDifToggleEnabled));

      sram_execution_test();
    }
  } else if (lc_ctrl_testutils_debug_func_enabled(&lc)) {
    sram_execution_test();
  } else {
    LOG_FATAL("Execution from SRAM cannot be enabled, cannot run the test");
  }

  return true;
}
