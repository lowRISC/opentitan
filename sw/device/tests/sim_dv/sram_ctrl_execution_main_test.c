// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/dif/dif_sram_ctrl.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/lc_ctrl_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/sram_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_isrs.h"
#include "sw/device/lib/testing/test_framework/ottf_macros.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/status.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"  // Generated

OTTF_DEFINE_TEST_CONFIG();

static dif_sram_ctrl_t sram_ctrl;

/**
 * This flag is used to verify that the execution from SRAM was successful.
 * Declared as volatile, because it is referenced in the fault handler, as well
 * as the main test flow.
 */
static volatile bool exception_observed;

/**
 * Main SRAM start and end addresses (inclusive).
 */
static const uint32_t kRamStartAddr = TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_BASE_ADDR;
static const uint32_t kRamEndAddr = TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_BASE_ADDR +
                                    TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_SIZE_BYTES -
                                    1;

/**
 * OTP HW partition relative IFETCH offset in bytes.
 */
static const uint32_t kOtpIfetchHwRelativeOffset =
    OTP_CTRL_PARAM_EN_SRAM_IFETCH_OFFSET - OTP_CTRL_PARAM_HW_CFG1_OFFSET;

/**
 * Executes the return instruction from MAIN SRAM.
 *
 * This function will return on success, or cause an exception if the
 * execution is disabled.
 */
OT_NAKED
OT_SECTION(".data")
void execute_code_in_sram(void) { asm volatile("jalr zero, 0(ra)"); }

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

  CHECK_DIF_OK(dif_otp_ctrl_dai_read_start(&otp, kDifOtpCtrlPartitionHwCfg1,
                                           kOtpIfetchHwRelativeOffset));

  CHECK_STATUS_OK(otp_ctrl_testutils_wait_for_dai(&otp));

  uint32_t value;
  CHECK_DIF_OK(dif_otp_ctrl_dai_read32_end(&otp, &value));

  return bitfield_field32_read(
             value, (bitfield_field32_t){.mask = 0xff, .index = 0}) ==
         kMultiBitBool8True;
}

/**
 * Overrides the default OTTF exception handler.
 *
 * This exception handler only processes the faults that are relevant to this
 * test. It falls into an infinite `wait_for_interrupt` routine (by calling
 * `abort()`) for the rest.
 *
 * The controlled fault originates in the retention SRAM, which means that
 * normally the return address would be calculated relative to the trapped
 * instruction. However, due to execution from retention SRAM being permanently
 * disabled, this approach would not work.
 *
 * Instead the control flow needs to be returned to the caller. In other words,
 * sram_execution_test -> retention_sram -> exception_handler
 * -> sram_execution_test.
 *
 * Before the jump into the exception handler, the register set is saved on
 * stack by the OTTF exception handler entry subroutine, which means that the
 * return address can be loaded from there. See comments below for more details.
 */
void ottf_exception_handler(uint32_t *exc_info) {
  // The frame address is the address of the stack location that holds the
  // `mepc`, since the OTTF exception handler entry code saves the `mepc` to
  // the top of the stack before transferring control flow to the exception
  // handler function (which is overridden here). See the `handler_exception`
  // subroutine in `sw/device/lib/testing/testing/ottf_isrs.S` for more details.
  uintptr_t mepc_stack_addr = (uintptr_t)OT_FRAME_ADDR();

  // The return address of the function that holds the trapping instruction is
  // the second top-most value placed on the stack by the OTTF exception handler
  // entry code. We grab this off the stack so that we can use it to overwrite
  // the `mepc` value stored on the stack, so that the `ottf_isr_exit`
  // subroutine (in `sw/device/lib/testing/test_framework/ottf_isrs.S`) will
  // restore control flow to the `sram_execution_test` function as described
  // above.
  uintptr_t ret_addr = *(uintptr_t *)(mepc_stack_addr + OTTF_WORD_SIZE);

  LOG_INFO("Handling exception: mepc = %p, (trapped) return address = %p",
           ibex_mepc_read(), ret_addr);

  uint32_t mcause = ibex_mcause_read();
  ibex_exc_t exception = mcause & kIbexExcMax;

  switch (exception) {
    case kIbexExcInstrAccessFault:
      LOG_INFO("Instruction access fault handler");
      exception_observed = true;
      *(uintptr_t *)mepc_stack_addr = ret_addr;
      break;
    case kIbexExcIllegalInstrFault:
      LOG_INFO("Illegal instruction fault handler");
      exception_observed = true;
      *(uintptr_t *)mepc_stack_addr = ret_addr;
      break;
    default:
      LOG_FATAL("Unexpected exception id = 0x%x", exception);
      abort();
  }
}

/**
 * Sets the sram_ctrl exec CSR to both states and attempts to execute
 * the code in SRAM. Checks whether an exception was observed for each
 * case in line with the expected result based on LC_STATE and
 * OTP IFETCH.
 */
void do_execute_test(bool debug_func, bool ifetch_en) {
  bool csr_enabled_exception_expected;
  bool csr_disabled_exception_expected;

  if (debug_func && !ifetch_en) {
    csr_enabled_exception_expected = false;
    csr_disabled_exception_expected = false;
  } else if (debug_func && ifetch_en) {
    csr_enabled_exception_expected = false;
    csr_disabled_exception_expected = true;
  } else if (!debug_func && !ifetch_en) {
    csr_enabled_exception_expected = true;
    csr_disabled_exception_expected = true;
  } else {
    csr_enabled_exception_expected = false;
    csr_disabled_exception_expected = true;
  }

  CHECK_DIF_OK(dif_sram_ctrl_exec_set_enabled(&sram_ctrl, kDifToggleEnabled));
  exception_observed = false;
  icache_invalidate();
  execute_code_in_sram();
  CHECK(exception_observed == csr_enabled_exception_expected,
        "Expected exception not observed whilst executing from SRAM!");
  CHECK_DIF_OK(dif_sram_ctrl_exec_set_enabled(&sram_ctrl, kDifToggleDisabled));
  exception_observed = false;
  icache_invalidate();
  execute_code_in_sram();
  CHECK(exception_observed == csr_disabled_exception_expected,
        "Expected exception not observed whilst executing from SRAM!");
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
  uintptr_t func_address = (uintptr_t)execute_code_in_sram;
  CHECK(func_address >= kRamStartAddr && func_address <= kRamEndAddr,
        "Test code resides outside of the Main SRAM: function address = %x",
        func_address);

  CHECK_DIF_OK(dif_sram_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR),
      &sram_ctrl));

  bool locked;
  CHECK_DIF_OK(
      dif_sram_ctrl_is_locked(&sram_ctrl, kDifSramCtrlLockExec, &locked));
  CHECK(!locked, "Execution is disabled and locked, cannot perform the test");

  dif_lc_ctrl_t lc;
  CHECK_DIF_OK(dif_lc_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_REGS_BASE_ADDR), &lc));

  bool debug_func = false;
  CHECK_STATUS_OK(lc_ctrl_testutils_debug_func_enabled(&lc, &debug_func));
  // For the current configuration (set by the testbench)
  // check that execution exceptions are as expected.
  do_execute_test(debug_func, otp_ifetch_enabled());

  // When the test is complete flag WFI status so
  // the testbench can reset and progress to the next
  // combination of LC_STATE and OTP IFETCH.
  test_status_set(kTestStatusInWfi);
  wait_for_interrupt();

  return true;
}
