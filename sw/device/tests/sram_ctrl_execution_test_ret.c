// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/dif/dif_sram_ctrl.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/sram_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf.h"
#include "sw/device/lib/testing/test_framework/ottf_isrs.h"
#include "sw/device/lib/testing/test_framework/ottf_macros.h"
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
void ottf_exception_handler(void) {
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

  LOG_INFO("Handling exception: mepc = %p, (trapped) return address = %p ",
           ibex_mepc_read(), ret_addr);

  uint32_t mcause = ibex_mcause_read();
  ottf_exc_id_t exception_id = mcause & kIdMax;

  switch (exception_id) {
    case kInstrAccessFault:
      LOG_INFO("Instruction access fault handler");
      instruction_access_fault = true;
      *(uintptr_t *)mepc_stack_addr = ret_addr;
      break;
    case kIllegalInstrFault:
      LOG_INFO("Illegal instruction fault handler");
      instruction_access_fault = false;
      *(uintptr_t *)mepc_stack_addr = ret_addr;
      break;
    default:
      LOG_FATAL("Unexpected exception id = 0x%x", exception_id);
      abort();
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
