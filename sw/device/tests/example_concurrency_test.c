// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * This example serves as a starting point for writing software top-level
 * concurrency tests that use the OpenTitan Test Framework (OTTF), and run at
 * the flash boot stage. This example is intended to be copied and modified
 * according to the instructions below.
 *
 * This example demonstrates a concurrency test that spawns three FreeRTOS
 * tasks, in addition to the `test_main` task. Each task is defined using a
 * separate function that never returns, and deletes itself after executing its
 * code. Since the priorities of each task are the same, yet higher than the
 * priority of the "test_main" task, calling `ottf_task_yield()` will switch
 * control flow between these tasks, until each task deletes itself. Then, the
 * `test_main` task will continue executing, returning `true` when the overall
 * test passes, triggering the OTTF to signal test execution has completed.
 *
 * Additionally, an example assertion failure is commented out below in `task_3`
 * to demonstrate how the test will terminate execution immediately upon
 * encountering said behavior in any task. The test runner (opentitantool) on
 * Verilator and FPGA platforms is monitoring the UART for a failure message
 * that gets printed immediately upon an assertion failure. It terminates the
 * test immediately upon seeing said message. Similarly, in DV, the testbench is
 * monitoring a specific memory location that gets written to on an assertion
 * failure.
 */

#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_macros.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

OTTF_DEFINE_TEST_CONFIG(.enable_concurrency = true,
                        .can_clobber_uart = false, );

static void task_1(void *task_parameters) {
  // ***************************************************************************
  // Place test code below.
  // ***************************************************************************
  LOG_INFO("Executing %s ...", ottf_task_get_self_name());
  ottf_task_yield();
  LOG_INFO("Continuing to execute %s ...", ottf_task_get_self_name());

  // ***************************************************************************
  // Delete the current task and never return.
  // ***************************************************************************
  OTTF_TASK_DELETE_SELF_OR_DIE;
}

static void task_2(void *task_parameters) {
  // ***************************************************************************
  // Place test code below.
  // ***************************************************************************
  LOG_INFO("Executing %s ...", ottf_task_get_self_name());

  // ***************************************************************************
  // Delete the current task and never return.
  // ***************************************************************************
  OTTF_TASK_DELETE_SELF_OR_DIE;
}

static void task_3(void *task_parameters) {
  // ***************************************************************************
  // Place test code below.
  // ***************************************************************************
  LOG_INFO("Executing %s ...", ottf_task_get_self_name());

  // ***************************************************************************
  // Uncomment to see the effects of a failed assertion. Delete this when
  // implementing a test.
  // ***************************************************************************
  // CHECK(false, "A failed assertion causes immediate test termination.");

  // ***************************************************************************
  // Delete the current task and never return.
  // ***************************************************************************
  OTTF_TASK_DELETE_SELF_OR_DIE;
}

bool test_main(void) {
  // ***************************************************************************
  // Create the FreeRTOS tasks that will comprise this test. Ensure the priority
  // levels of each task are higher than the priority of the current "test_main"
  // task, which is 0.
  // ***************************************************************************
  LOG_INFO("Starting to execute %s ...", ottf_task_get_self_name());
  CHECK(ottf_task_create(task_1, "task_1", kOttfFreeRtosMinStackSize, 1));
  CHECK(ottf_task_create(task_2, "task_2", kOttfFreeRtosMinStackSize, 1));
  CHECK(ottf_task_create(task_3, "task_3", kOttfFreeRtosMinStackSize, 1));

  // ***************************************************************************
  // Yield control flow to the highest priority task in the run queue. Since the
  // tasks created above all have a higher priority level than the current
  // "test_main" task, execution will not be returned to the current task until
  // the above tasks have been deleted.
  // ***************************************************************************
  LOG_INFO("Yielding execution to another task.");
  ottf_task_yield();

  // ***************************************************************************
  // Return true if the test succeeds. Return false if it should fail.
  // ***************************************************************************
  return true;
}
