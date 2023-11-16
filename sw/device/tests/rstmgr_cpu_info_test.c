// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_isrs.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

/**
 * RSTMGR CPU INFO TEST
 *
 * This has three stages:
 *
 * 1. After the first startup, an illegal memory access is performed.
 *    In the exception handler, a software reset is triggered.
 *
 * 2. After the software reset, the CPU info dump is checked against
 *    the expected values for this single fault. The watch dog is then set up
 *    and another illegal memory access is performed. Only this time
 *    the exception handler performs another illegal read.
 *    Causing the ibex to be haulted by the alert handler.
 *    The watch dog will eventually trigger a reset.
 *
 * 3. After the watchdog reset, the CPU info dump is checked against
 *    the expected values for this double fault.
 */

// CPU Dump Size and Unmapped Addresses.
enum {
  kCpuDumpSize = 8,
  kIllegalAddr0 = 0xF0000000,
  kIllegalAddr1 = 0xF0000004,
  kIllegalAddr2 = 0x00000008,
};

// Declaring the labels used to calculate the expected current and next pc
// after a double fault.
extern const uint32_t _ottf_interrupt_vector;

// The labels to points in the code of which the memory address is needed.
extern const char kSingleFaultAddr[];
extern const char kSingleFaultAddrCurrentPc[];
extern const char kSingleFaultAddrNextPc[];
extern const char kDoubleFaultFirstAddr[];
extern const char kDoubleFaultSecondAddr[];

// A handle to the reset manager.
static dif_rstmgr_t rstmgr;

// This variable is used to ensure loads from an address aren't optimised out.
volatile static uint32_t addr_val;

/**
 * When true, the exception handler will trigger another fault,
 * causing a double fault,
 * otherwise it triggers a software reset.
 */
volatile static bool double_fault;

/**
 * Overrides the default OTTF exception handler.
 */
void ottf_exception_handler(void) {
  if (double_fault) {
    OT_ADDRESSABLE_LABEL(kDoubleFaultSecondAddr);
    mmio_region_write32(mmio_region_from_addr(kIllegalAddr2), 0, 0);
  } else {
    CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));
    // Write to `addr_val` so that the 'last data access' address is
    // a known value (the address of addr_val).
    addr_val = 1;
    OT_ADDRESSABLE_LABEL(kSingleFaultAddrCurrentPc);
    wait_for_interrupt();  // Wait for the reset.
    OT_ADDRESSABLE_LABEL(kSingleFaultAddrNextPc);
    addr_val = 2;
  }
  CHECK(false,
        "This point should be unreachable; "
        "a reset or another fault should have occured.");
}

/**
 * Gets, parses and returns the cpu info crash dump.
 *
 * @param ibex A handle to the ibex.
 * @return The cpu info crash dump.
 */
static dif_rv_core_ibex_crash_dump_info_t get_dump(
    const dif_rv_core_ibex_t *ibex) {
  size_t size_read;
  dif_rstmgr_cpu_info_dump_segment_t dump[DIF_RSTMGR_CPU_INFO_MAX_SIZE];

  CHECK_DIF_OK(dif_rstmgr_cpu_info_dump_read(
      &rstmgr, dump, DIF_RSTMGR_CPU_INFO_MAX_SIZE, &size_read));
  CHECK(size_read == kCpuDumpSize,
        "The observed cpu info dump's size was %d, "
        "but it was expected to be %d",
        size_read, kCpuDumpSize);

  dif_rv_core_ibex_crash_dump_info_t output;
  CHECK_DIF_OK(
      dif_rv_core_ibex_parse_crash_dump(ibex, dump, size_read, &output));
  return output;
}

/**
 * Checks the 'current' section of the cpu info dump against the given expected
 * values.
 *
 * For double faults the PCs may differ from the expected ones due to pipeline
 * stalls.
 *
 * @param obs_state The cpu info crash dump's current state values.
 * @param exp_state The expected values of the current state.
 * @param double_fault The states correspond to a double fault.
 */
static void check_state(dif_rv_core_ibex_crash_dump_state_t obs_state,
                        dif_rv_core_ibex_crash_dump_state_t exp_state,
                        dif_toggle_t double_fault) {
  CHECK(exp_state.mtval == obs_state.mtval,
        "Last Exception Access Addr: Expected 0x%x != Observed 0x%x",
        exp_state.mtval, obs_state.mtval);
  LOG_INFO("exp_mcpc=0x%x, exp_mnpc=0x%x, obs_mcpc=0x%x, obs_mnpc=0x%x",
           exp_state.mcpc, exp_state.mnpc, obs_state.mcpc, obs_state.mnpc);
  // Check the current pc is either the expected or expected + 4, since the
  // pipeline may have stalled.
  CHECK(exp_state.mcpc == obs_state.mcpc ||
            (double_fault == kDifToggleEnabled &&
             exp_state.mcpc - 4 == obs_state.mcpc),
        "Current PC: Observed 0x%x not within 4 bytes of Expected 0x%x",
        obs_state.mcpc, exp_state.mcpc);
  CHECK(exp_state.mnpc == obs_state.mnpc,
        "Next PC: Expected 0x%x != Observed 0x%x", exp_state.mnpc,
        obs_state.mnpc);
  CHECK(exp_state.mdaa == obs_state.mdaa,
        "Last Data Access Addr: Expected 0x%x != Observed 0x%x", exp_state.mdaa,
        obs_state.mdaa);
  CHECK(exp_state.mpec == obs_state.mpec,
        "The Observed MPEC, 0x%x, was not in the expected 0x%x", obs_state.mpec,
        exp_state.mpec);
}

/**
 * Checks the 'previous' section of the cpu info dump against the given expected
 * values.
 *
 * @param obs_prev_state The cpu info crash dump's previous state values.
 * @param exp_prev_state The expected values of the previous state.
 */
static void check_prev_state(
    dif_rv_core_ibex_previous_crash_dump_state_t obs_prev_state,
    dif_rv_core_ibex_previous_crash_dump_state_t exp_prev_state) {
  CHECK(exp_prev_state.mtval == obs_prev_state.mtval,
        "Last Exception Access Addr: Expected 0x%x != Observed 0x%x",
        exp_prev_state.mtval, obs_prev_state.mtval);
  CHECK(exp_prev_state.mpec == obs_prev_state.mpec,
        "The Observed Previous MPEC, 0x%x, "
        "was not in the expected 0x%x",
        obs_prev_state.mpec, exp_prev_state.mpec);
}

bool test_main(void) {
  dif_rv_core_ibex_crash_dump_info_t dump;

  dif_aon_timer_t aon_timer;
  dif_pwrmgr_t pwrmgr;
  dif_rv_core_ibex_t ibex;

  // Initialize Handles.
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));
  CHECK_DIF_OK(dif_aon_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR), &aon_timer));
  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));
  CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR), &ibex));

  switch (rstmgr_testutils_reason_get()) {
    case kDifRstmgrResetInfoPor:  // The first power-up.
      LOG_INFO("Triggering single fault.");

      // Enable cpu info.
      CHECK_DIF_OK(dif_rstmgr_cpu_info_set_enabled(&rstmgr, kDifToggleEnabled));

      double_fault = false;
      OT_ADDRESSABLE_LABEL(kSingleFaultAddr);
      addr_val = mmio_region_read32(mmio_region_from_addr(kIllegalAddr0), 0);
      CHECK(false,
            "This should be unreachable; a single fault should have occurred.");
      break;

    case kDifRstmgrResetInfoSw:  // The power-up after the single fault.
      LOG_INFO("Checking CPU info dump after single fault.");

      dump = get_dump(&ibex);

      CHECK(
          dump.double_fault == kDifToggleDisabled,
          "CPU Info dump shows a double fault after experiencing only a single "
          "fault.");

      check_state(dump.fault_state,
                  (dif_rv_core_ibex_crash_dump_state_t){
                      .mtval = (uint32_t)kIllegalAddr0,
                      .mpec = (uint32_t)kSingleFaultAddr + 4,
                      .mdaa = (uint32_t)&addr_val,
                      .mcpc = (uint32_t)kSingleFaultAddrCurrentPc,
                      .mnpc = (uint32_t)kSingleFaultAddrNextPc,
                  },
                  kDifToggleDisabled);

      LOG_INFO("Setting up watch dog and triggering a double fault.");
      // When we boot through the ROM the watchdog is configured to generate an
      // NMI on barking, so we want the watchdog to bark before the first
      // exception to avoid the NMI messing with the fault dump.
      uint32_t bark_cycles = 0;
      CHECK_STATUS_OK(
          aon_timer_testutils_get_aon_cycles_from_us(1, &bark_cycles));
      uint32_t bite_cycles = 0;
      CHECK_STATUS_OK(
          aon_timer_testutils_get_aon_cycles_from_us(100, &bite_cycles));

      // Set wdog as a reset source.
      CHECK_DIF_OK(dif_pwrmgr_set_request_sources(
          &pwrmgr, kDifPwrmgrReqTypeReset, kDifPwrmgrResetRequestSourceTwo,
          kDifToggleEnabled));
      // Setup the watchdog bark and bite timeouts.
      CHECK_STATUS_OK(aon_timer_testutils_watchdog_config(
          &aon_timer, bark_cycles, bite_cycles, false));
      // Enable cpu info.
      CHECK_DIF_OK(dif_rstmgr_cpu_info_set_enabled(&rstmgr, kDifToggleEnabled));

      double_fault = true;
      OT_ADDRESSABLE_LABEL(kDoubleFaultFirstAddr);
      addr_val = mmio_region_read32(mmio_region_from_addr(kIllegalAddr1), 0);
      CHECK(false,
            "This should be unreachable; a double fault should have occured.");
      break;

    case kDifRstmgrResetInfoWatchdog:  // The power-up after the double fault.
      LOG_INFO("Checking CPU info dump after double fault.");

      dump = get_dump(&ibex);

      CHECK(dump.double_fault == kDifToggleEnabled,
            "CPU Info dump doesn't show a double fault has happened.");

      // After #15219 was merged, the execution stops more predictably
      // once fetch_en is dropped due to a double fault.
      // The current pc should now correspond to the instruction after the
      // cause of the illegal load or that same instruction, depending on
      // whether the pipeline stalled.
      // The next pc is always the exception handler, because that's
      // where execution would have gone if it had not halted
      check_state(dump.fault_state,
                  (dif_rv_core_ibex_crash_dump_state_t){
                      .mtval = (uint32_t)kIllegalAddr2,
                      .mpec = (uint32_t)kDoubleFaultSecondAddr,
                      .mdaa = (uint32_t)kIllegalAddr2,
                      .mcpc = (uint32_t)kDoubleFaultSecondAddr + 4,
                      .mnpc = (uint32_t)&_ottf_interrupt_vector,
                  },
                  kDifToggleEnabled);

      check_prev_state(dump.previous_fault_state,
                       (dif_rv_core_ibex_previous_crash_dump_state_t){
                           .mtval = (uint32_t)kIllegalAddr1,
                           .mpec = (uint32_t)kDoubleFaultFirstAddr + 4,
                       });

      return true;

    default:
      CHECK(false, "Device was reset by an unexpected source.");
      break;
  }
  return false;
}
