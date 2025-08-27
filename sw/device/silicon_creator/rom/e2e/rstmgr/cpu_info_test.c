// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/testing/rv_core_ibex_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "hw/top/rstmgr_regs.h"

OTTF_DEFINE_TEST_CONFIG();

enum {
  kCpuDumpSize = 8,
  kIllegalAddr0 = 0xF0000000,
};

// The labels to points in the code of which the memory address is needed.
extern const char kFaultAddrStart[];
extern const char kFaultAddrEnd[];

// This variable is used to ensure loads from an address aren't optimised out.
volatile static uint32_t addr_val;

/**
 * Overrides the default OTTF exception handler.
 */
void ottf_exception_handler(uint32_t *exc_info) {
  OT_DISCARD(exc_info);
  rstmgr_reset();
}

static void check_cpu_info_dump(void) {
  LOG_INFO("Checking CPU info dump after fault.");

  rstmgr_info_t info;

  rstmgr_cpu_info_collect(&info);
  CHECK(info.length == kCpuDumpSize,
        "The observed cpu info dump's size was %d, "
        "but it was expected to be %d",
        info.length, kCpuDumpSize);

  dif_rv_core_ibex_crash_dump_state_t dump =
      ((dif_rv_core_ibex_crash_dump_info_t *)info.info)->fault_state;

  RV_CORE_IBEX_TESTUTILS_PRINT_CRASH_DUMP(dump);

#if defined(TEST_CPU_INFO_ENABLED)
  uint32_t start = (uint32_t)kFaultAddrStart;
  uint32_t end = (uint32_t)kFaultAddrEnd;

  CHECK(kIllegalAddr0 == dump.mtval,
        "Last Exception Access Addr: Expected 0x%x != Observed 0x%x",
        kIllegalAddr0, dump.mtval);
  CHECK(start <= dump.mpec && dump.mpec <= end,
        "The Observed MPEC, 0x%x, was not in the expected range [0x%x, 0x%x]",
        dump.mpec, start, end);
#elif defined(TEST_CPU_INFO_DISABLED)
  CHECK(dump.mtval == 0, "mtval should be zero, got 0x%x", dump.mtval);
  CHECK(dump.mpec == 0, "mpec should be zero, got 0x%x", dump.mpec);
  CHECK(dump.mdaa == 0, "mdaa should be zero, got 0x%x", dump.mdaa);
  CHECK(dump.mnpc == 0, "mnpc should be zero, got 0x%x", dump.mnpc);
  CHECK(dump.mcpc == 0, "mcpc should be zero, got 0x%x", dump.mcpc);
#else
#error "no cpu info test variant is defined"
#endif
}

bool test_main(void) {
  uint32_t reset_reasons = retention_sram_get()->creator.reset_reasons;
  switch (reset_reasons) {
    case 1 << kRstmgrReasonPowerOn:
      LOG_INFO("Triggering fault.");

      OT_ADDRESSABLE_LABEL(kFaultAddrStart);
      addr_val = mmio_region_read32(mmio_region_from_addr(kIllegalAddr0), 0);
      OT_ADDRESSABLE_LABEL(kFaultAddrEnd);
      return false;
    case 1 << kRstmgrReasonSoftwareRequest:
      LOG_INFO("Escalation detected!");
      check_cpu_info_dump();
      return true;
    default:
      LOG_INFO("Unhandled reset reason: %d", reset_reasons);
      return false;
  }

  return false;
}
