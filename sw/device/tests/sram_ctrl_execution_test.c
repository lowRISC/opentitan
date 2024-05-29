// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/dif/dif_sram_ctrl.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_isrs.h"
#include "sw/device/lib/testing/test_framework/ottf_macros.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/epmp_state.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

static dif_sram_ctrl_t sram_ctrl;

enum {
  kSramStart = TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_BASE_ADDR,
  kSramEnd = TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_BASE_ADDR +
             TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_SIZE_BYTES,
  kSramRetStart = TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR,
};

OT_SECTION(".data.sram_function_test")
OT_NOINLINE
static void sram_function_test(void) {
  uint32_t pc = 0;
  asm("auipc %[pc], 0;" : [pc] "=r"(pc));
  LOG_INFO("PC: %p, SRAM: [%p, %p)", pc, kSramStart, kSramEnd);
  CHECK(pc >= kSramStart && pc < kSramEnd, "PC is outside the main SRAM");
}

// Redeclaration of the addressable symbol in `sram_ret_neg_test()` to be used
// in `ottf_exception_handler()`.
extern const char kSramRetNegTestReturn[];

void ottf_exception_handler(uint32_t *exc_info) {
  // The frame address is the address of the stack location that holds the
  // `mepc`, since the OTTF exception handler entry code saves the `mepc` to
  // the top of the stack before transferring control flow to the exception
  // handler function (which is overridden here). See the `handler_exception`
  // subroutine in `sw/device/lib/testing/testing/ottf_isrs.S` for more details.
  uintptr_t *mepc_stack_addr = (uintptr_t *)OT_FRAME_ADDR();
  ibex_exc_t exception = ibex_mcause_read();
  switch (exception) {
    case kIbexExcInstrAccessFault:
      LOG_INFO("Detected instruction access fault");
      *mepc_stack_addr = (uintptr_t)kSramRetNegTestReturn;
      break;
    default:
      LOG_FATAL("Unexpected exception id = 0x%x", exception);
      abort();
  }
}

static void sram_ret_neg_test(void) {
  memset((void *)kSramRetStart, 0, sizeof(uint32_t));
  ((void (*)(void))kSramRetStart)();
  CHECK(false, "Should not be here");
  OT_ADDRESSABLE_LABEL(kSramRetNegTestReturn);
}

bool test_main(void) {
  CHECK_DIF_OK(dif_sram_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR),
      &sram_ctrl));

  // Unlock the entire address space for RWX so that we can run this test with
  // both rom and test_rom.
  CSR_WRITE(CSR_REG_PMPADDR7, 0x7fffffff);

  uint32_t pmpcfg1 = 0;
  CSR_READ(CSR_REG_PMPCFG1, &pmpcfg1);
  CHECK((pmpcfg1 & 0xff000000) == 0,
        "expected PMPCFG1 to be unconfigured before changing it");

  CSR_SET_BITS(CSR_REG_PMPCFG1,
               (kEpmpModeNapot | kEpmpPermLockedReadWriteExecute) << 24);

  // Note: We can test the negative case only using the retention SRAM since
  // execution is unconditionally enabled for the main SRAM in the RMA life
  // cycle state.
  sram_ret_neg_test();

  // Try to enable SRAM execution.
  dif_result_t exec_enabled =
      dif_sram_ctrl_exec_set_enabled(&sram_ctrl, kDifToggleEnabled);

  // If SRAM execution was not enabled, re-check that execution fails, else
  // check the positive case.
  if (exec_enabled == kDifLocked) {
    sram_ret_neg_test();
  } else {
    CHECK_DIF_OK(exec_enabled);
    sram_function_test();
  }

  return true;
}
