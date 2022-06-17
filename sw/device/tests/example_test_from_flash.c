// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * This template serves as a starting point for writing software chip-level
 * tests that use the OpenTitan Test Framework (OTTF). This template is intended
 * to be copied and modified according to the instructions below.
 *
 * Plese delete all instructional comments after editing this template.
 */

/**
 * Uncomment if you want to initialize the non-volatile scratch region below
 * using UINT32_MAX.
 */
// #include <stdint.h>

/**
 * Uncomment if you want to log messages with `LOG_{INFO,WARNING,ERROR,FATAL()`.
 */
// #include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

/**
 * The OTTF expects the `kTestConfig` symbol to be present, as it contains
 * configuration settings for running the test implemented in this file. DO NOT
 * delete this macro. However, you may modify the member assignments below
 * according to the instructions above each configuration member.
 *
 * Set `enable_concurrency` to true if this test should run as a FreeRTOS
 * task (enabling the test to spawn additional concurrent FreeRTOS tasks).
 * When `enable_concurrency` is set to false, this test will run as a
 * bare-metal program. Note, for the majority of chip-level tests, this
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
 * Place data in flash that will need to persist across resets by marking with
 * with the section ".non_volatile_scratch"). Write to this region with the
 * flash controller DIFs. Read from it with `abs_mmio_read32(...)`.
 * Additionally, be sure to initialize the bits in this array to all 1s,
 * otherwise this region may not be programmed properly, depending on the
 * programming transactions issued. According to the hardware specification:
 *  - a bit cannot be programmed back to 1 once it has been programmed to 0, and
 *  - only erase can restore a bit to 1 under normal circumstances.
 */
// __attribute__((section(".non_volatile_scratch")))
// const volatile uint32_t non_volatile_data[2] = {UINT32_MAX, UINT32_MAX};

bool test_main(void) {
  /**
   * Place test code here.
   */

  /**
   * Return true if the test succeeds. Return false if it should fail.
   */
  return true;
}
