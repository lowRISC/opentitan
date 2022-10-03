// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * This template serves as a starting point for writing software top-level
 * tests that use the OpenTitan Test Framework (OTTF), and run at the flash
 * boot stage. This template is intended to be copied and modified according to
 * the instructions below.
 *
 * Plese delete all instructional comments after editing this template.
 */

/**
 * Uncomment if you want to log messages with `LOG_{INFO,WARNING,ERROR,FATAL()`.
 */
// #include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

/**
 * The OTTF expects the `kOttfTestConfig` symbol to be present, as it contains
 * configuration settings for running the test implemented in this file. DO NOT
 * delete this macro. However, you may modify the member assignments below
 * according to the instructions above each configuration member.
 *
 * Set `enable_concurrency` to true if this test should run as a FreeRTOS
 * task (enabling the test to spawn additional concurrent FreeRTOS tasks).
 * When `enable_concurrency` is set to false, this test will run as a
 * bare-metal program. Note, for the majority of top-level tests, this
 * should be set to false.
 *
 * Set `can_clobber_uart` to true if this test will reconfigure the UART in
 * any way, since the OTTF uses the UART to communicate test results on
 * Verilator and FPGA platforms, it must be reconfigured by the OTTF before
 * test results are printed.
 */
OTTF_DEFINE_TEST_CONFIG(.enable_concurrency = false,
                        .can_clobber_uart = false, );

/**
 * Override any of the default OTTF exception handlers (by uncommenting and
 * implementing them) if this test requires non-default exeception handling
 * logic. Delete those that do not need to be overridden.
 *
 * See `sw/device/lib/testing/test_framework/ottf_isrs.c` for implementation
 * details of the default OTTF exception handlers.
 */
// void ottf_exception_handler(void) {}
// void ottf_instr_misaligned_fault_handler(void) {}
// void ottf_instr_access_fault_handler(void) {}
// void ottf_illegal_instr_fault_handler(void) {}
// void ottf_breakpoint_handler(void) {}
// void ottf_load_store_fault_handler(void) {}
// void ottf_machine_ecall_handler(void) {}
// void ottf_user_ecall_handler(void) {}

/**
 * Override any of the default OTTF ISRs (by uncommenting and implementing them)
 * if this test requires non-default ISR logic. Delete those that do not need to
 * be overridden.
 *
 * See `sw/device/lib/testing/test_framework/ottf_isrs.c` for implementation
 * details of the default OTTF ISRs.
 */
// void ottf_software_isr(void) {}
// void ottf_timer_isr(void) {}
// void ottf_external_isr(void) {}

/**
 * Save data that will need to persist across resets by placing it in the
 * ".non_volatile_scratch" section. OpenTitan's flash is mapped to its address
 * space for reads. Thus, these variables can be read as usual. Write to this
 * region with the flash controller DIFs, obeying flash constraints. Since the
 * non-volatile scratch region is NOLOAD and bootstrap erases all flash, initial
 * values of variables in this section are always `0xff`, regardless of any
 * initialization in the source code. In order to avoid confusion, don't
 * initialize or assign to these values. If needed, they can be initialized at
 * runtime via flash controller DIFs.
 */
// OT_SECTION(".non_volatile_scratch") uint32_t non_volatile_data[2];

bool test_main(void) {
  /**
   * Place test code here.
   */

  /**
   * Return true if the test succeeds. Return false if it should fail.
   */
  return true;
}
