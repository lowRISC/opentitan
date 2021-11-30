// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/dif/dif_sram_ctrl.h"
#include "sw/device/lib/handler.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/sram_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/test_main.h"
#include "sw/device/lib/testing/test_framework/test_status.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

const test_config_t kTestConfig;

static dif_sram_ctrl_t sram_ctrl;

/**
 * This flag is used to verify that the instruction access fault has occurred,
 * and has been successfully serviced. Declared as volatile, because it is
 * referenced in the fault handler, as well as the main test flow.
 */
static volatile bool instruction_access_fault;

static const uint32_t kRetRamStartAddr =
    TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR;
static const uint32_t kRetRamEndAddr =
    TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR +
    TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_SIZE_BYTES - 1;

/**
 * Handles an exception.
 *
 * This exception handler only processes the faults that are relevant. It falls
 * into an infinite `wait_for_interrupt` routine for the rest.
 *
 * The controlled fault originates in the retention SRAM, which means that
 * normally the return address would be calculated relative to the offending
 * instruction. However, due to execution from retention SRAM being permanently
 * disabled, this approach would not work.
 *
 * Instead the control needs to be returned to the caller. In other words
 * sram_execution_test -> retention_sram -> exception_handler
 * -> sram_execution_test.
 *
 * Before the jump into the exception handler, the register set is saved on
 * stack, which means that the return address can be loaded from there.
 */
void handler_exception(void) {
  uintptr_t ret_addr = (uintptr_t)OT_RETURN_ADDR();
  LOG_INFO("Fault address: mepc = 0x%x, return address = 0x%x",
           ibex_mepc_read(), ret_addr);

  exc_id_t exception_id = ibex_mcause_read();
  switch (exception_id) {
    case kInstAccFault:
      LOG_INFO("Instruction access fault handler");
      instruction_access_fault = true;
      ibex_mepc_write(ret_addr);
      break;
    case kInstIllegalFault:
      LOG_INFO("Instruction illegal fault handler");
      instruction_access_fault = false;
      ibex_mepc_write(ret_addr);
      break;
    default:
      LOG_FATAL("Unexpected exception id = 0x%x", exception_id);
      while (true) {
        wait_for_interrupt();
      }
  }
}

/**
 * Used to execute instructions in Retention SRAM.
 */
typedef void (*sram_ctrl_instruction_fault_function_t)(void);

/**
 * Performs SRAM execution test.
 *
 * `sram_ctrl_instruction_fault_function_t` is "mapped" onto the
 * block of memory in Retention SRAM starting at `kRetRamStartAddr` and the
 * size of `SRAM_CTRL_DATA_NUM_BYTES` that holds `unimp` instructions.
 *
 * Please see the following document for more context:
 * https://github.com/riscv-non-isa/riscv-asm-manual/blob/master/riscv-asm.md
 */
static void sram_execution_test(void) {
  memset((void *)kRetRamStartAddr, 0, SRAM_CTRL_TESTUTILS_DATA_NUM_BYTES);

  // Map the function pointer onto the instruction buffer.
  sram_ctrl_instruction_fault_function_t instruction_access_fault_func =
      (sram_ctrl_instruction_fault_function_t)kRetRamStartAddr;

  uintptr_t func_address = (uintptr_t)instruction_access_fault_func;
  CHECK(func_address >= kRetRamStartAddr && func_address <= kRetRamEndAddr,
        "Test code resides outside of the Ret SRAM: function address = %x",
        func_address);

  instruction_access_fault = false;
  instruction_access_fault_func();
  CHECK(instruction_access_fault, "Expected instruction access fault");
}

bool test_main(void) {
  CHECK_DIF_OK(dif_sram_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_BASE_ADDR),
      &sram_ctrl));

  sram_execution_test();

  return true;
}
