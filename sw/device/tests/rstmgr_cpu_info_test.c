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
 *  This test creates a double fault by accessing a register with
 *  a non-existing address.
 *  After the double fault, the DUT gets reset by the watchdog bite
 *  and the test collects / checks the cpu_info from the rstmgr.
 */

// CPU Dump Size and Unmapped Addresses.
enum {
  kCpuDumpSize = 8,
  kIllegalAddr1 = 0xF0000004,
  kIllegalAddr2 = 0xF0000008,
};

// Declaring the labels used to calculate the expected current and next pc.
extern const uint32_t _ottf_interrupt_vector, handler_exception;

// The labels to points in the code of which the memory address is needed.
extern const char kDoubleFaultFirstAddrLower[];
extern const char kDoubleFaultFirstAddrUpper[];
extern const char kDoubleFaultSecondAddrLower[];
extern const char kDoubleFaultSecondAddrUpper[];

/**
 * This variable is used to ensure loads from an address aren't optimised out.
 */
volatile static uint32_t addr_val;

/**
 * Overrides the default OTTF exception handler.
 */
void ottf_exception_handler(void) {
  OT_ADDRESSABLE_LABEL(kDoubleFaultSecondAddrLower);
  addr_val = mmio_region_read32(mmio_region_from_addr(kIllegalAddr2), 0);
  OT_ADDRESSABLE_LABEL(kDoubleFaultSecondAddrUpper);
}

/**
 * Gets, parses and returns the cpu info crash dump.
 *
 * @param rstmgr A handle to the reset manager.
 * @param ibex A handle to the ibex.
 * @return The cpu info crash dump.
 */
static dif_rv_core_ibex_crash_dump_info_t get_dump(
    const dif_rstmgr_t *rstmgr, const dif_rv_core_ibex_t *ibex) {
  size_t size_read;
  dif_rstmgr_cpu_info_dump_segment_t dump[DIF_RSTMGR_CPU_INFO_MAX_SIZE];

  CHECK_DIF_OK(dif_rstmgr_cpu_info_dump_read(
      rstmgr, dump, DIF_RSTMGR_CPU_INFO_MAX_SIZE, &size_read));
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
 * Holds the expected cpu info dump values for the current state.
 */
typedef struct rstmgr_cpu_info_test_exp_state {
  uint32_t mtval;   ///< The last exception address.
  uint32_t mpec_l;  ///< The last exception PC lower bound.
  uint32_t mpec_u;  ///< The last exception PC upper bound.
  uint32_t mdaa;    ///< The last data access address.
  uint32_t mnpc;    ///< The next PC.
  uint32_t mcpc;    ///< The current PC.
} rstmgr_cpu_info_test_exp_state_t;

/**
 * Holds the expected cpu info dump values for the previous state.
 */
typedef struct rstmgr_cpu_info_test_exp_prev_state {
  uint32_t mtval;  ///< The exception address for the previous crash.
  uint32_t
      mpec_l;  ///< The last exception PC lower bound for the previous crash.
  uint32_t
      mpec_u;  ///< The last exception PC upper bound for the previous crash.
} rstmgr_cpu_info_test_exp_prev_state_t;

/**
 * Checks the 'current' section of the cpu info dump against the given expected
 * values.
 *
 * @param obs_state The cpu info crash dump's current state values.
 * @param exp_state The expected values of the current state.
 */
static void check_state(dif_rv_core_ibex_crash_dump_state_t obs_state,
                        rstmgr_cpu_info_test_exp_state_t exp_state) {
  CHECK(exp_state.mtval == obs_state.mtval,
        "Last Exception Access Addr: Expected 0x%x != Observed 0x%x",
        exp_state.mtval, obs_state.mtval);
  CHECK(exp_state.mcpc == obs_state.mcpc,
        "Current PC: Expected 0x%x != Observed 0x%x", exp_state.mcpc,
        obs_state.mcpc);
  CHECK(exp_state.mnpc == obs_state.mnpc,
        "Next PC: Expected 0x%x != Observed 0x%x", exp_state.mnpc,
        obs_state.mnpc);
  CHECK(exp_state.mdaa == obs_state.mdaa,
        "Last Data Access Addr: Expected 0x%x != Observed 0x%x", exp_state.mdaa,
        obs_state.mdaa);
  CHECK(
      exp_state.mpec_l <= obs_state.mpec && obs_state.mpec < exp_state.mpec_u,
      "The Observed MPEC, 0x%x, was not in the expected range of [0x%x, 0x%x)",
      obs_state.mpec, exp_state.mpec_l, exp_state.mpec_u);
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
    rstmgr_cpu_info_test_exp_prev_state_t exp_prev_state) {
  CHECK(exp_prev_state.mtval == obs_prev_state.mtval,
        "Last Exception Access Addr: Expected 0x%x != Observed 0x%x",
        exp_prev_state.mtval, obs_prev_state.mtval);
  CHECK(exp_prev_state.mpec_l <= obs_prev_state.mpec &&
            obs_prev_state.mpec < exp_prev_state.mpec_u,
        "The Observed Previous MPEC, 0x%x, "
        "was not in the expected range of [0x%x, 0x%x)",
        obs_prev_state.mpec, exp_prev_state.mpec_l, exp_prev_state.mpec_u);
}

bool test_main(void) {
  dif_rstmgr_t rstmgr;
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

  dif_rstmgr_reset_info_bitfield_t rst_info = rstmgr_testutils_reason_get();

  if (rst_info == kDifRstmgrResetInfoPor) {
    LOG_INFO("Booting for the first time, setting wdog");

    uint32_t bark_cycles = aon_timer_testutils_get_aon_cycles_from_us(100);
    uint32_t bite_cycles = aon_timer_testutils_get_aon_cycles_from_us(100);

    // Set wdog as a reset source.
    CHECK_DIF_OK(dif_pwrmgr_set_request_sources(&pwrmgr, kDifPwrmgrReqTypeReset,
                                                kDifPwrmgrResetRequestSourceTwo,
                                                kDifToggleEnabled));
    // Setup the watchdog bark and bite timeouts.
    aon_timer_testutils_watchdog_config(&aon_timer, bark_cycles, bite_cycles,
                                        false);
    // Enable cpu info.
    CHECK_DIF_OK(dif_rstmgr_cpu_info_set_enabled(&rstmgr, kDifToggleEnabled));

    // Trigger a double fault.
    OT_ADDRESSABLE_LABEL(kDoubleFaultFirstAddrLower);
    addr_val = mmio_region_read32(mmio_region_from_addr(kIllegalAddr1), 0);
    OT_ADDRESSABLE_LABEL(kDoubleFaultFirstAddrUpper);
    CHECK(false,
          "This should be unreachable; a double fault should have occured.");
  } else {
    LOG_INFO("Comes back after bite");

    dif_rv_core_ibex_crash_dump_info_t dump = get_dump(&rstmgr, &ibex);

    CHECK(dump.double_fault == kDifToggleEnabled,
          "CPU Info dump doesn't show a double fault has happened.");

    // The current behaviour after a double fault is to capture, in the CPU info
    // dump, the interrupt vector below the one which was taken to jump to the
    // exception handler as the current PC and the start of the exception
    // handler as the next PC. This feels wrong. However, with a lack of a clear
    // definition of what these values should contain, the test enforces this
    // behaviour so that regressions can be caught.
    uint32_t curr_pc = (uint32_t)&_ottf_interrupt_vector + 4;
    uint32_t next_pc = (uint32_t)&handler_exception;

    check_state(dump.fault_state,
                (rstmgr_cpu_info_test_exp_state_t){
                    .mtval = (uint32_t)kIllegalAddr2,
                    .mpec_l = (uint32_t)kDoubleFaultSecondAddrLower,
                    .mpec_u = (uint32_t)kDoubleFaultSecondAddrUpper,
                    .mdaa = (uint32_t)kIllegalAddr2,
                    .mcpc = curr_pc,
                    .mnpc = next_pc,
                });

    check_prev_state(dump.previous_fault_state,
                     (rstmgr_cpu_info_test_exp_prev_state_t){
                         .mtval = (uint32_t)kIllegalAddr1,
                         .mpec_l = (uint32_t)kDoubleFaultFirstAddrLower,
                         .mpec_u = (uint32_t)kDoubleFaultFirstAddrUpper,
                     });

    // Turn off the AON timer hardware completely before exiting.
    aon_timer_testutils_shutdown(&aon_timer);
    return true;
  }

  return false;
}
