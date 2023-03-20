// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include <assert.h>
#include <stddef.h>

#include "external/freertos/include/FreeRTOS.h"
#include "external/freertos/include/queue.h"
#include "external/freertos/include/task.h"
#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/rand_testutils.h"
#include "sw/device/lib/testing/test_framework/FreeRTOSConfig.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/coverage.h"
#include "sw/device/lib/testing/test_framework/ottf_console.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/status.h"
#include "sw/device/silicon_creator/lib/manifest_def.h"

// TODO: make this toplevel agnostic.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Check layout of test configuration struct since OTTF ISR asm code requires a
// specific layout.
OT_ASSERT_MEMBER_OFFSET(ottf_test_config_t, enable_concurrency, 0);
OT_ASSERT_MEMBER_SIZE(ottf_test_config_t, enable_concurrency, 1);

// Pointer to the current FreeRTOS Task Control Block, which should be non-NULL
// when OTTF concurrency is enabled, and test code is executed within FreeRTOS
// tasks.
extern void *pxCurrentTCB;

// A global random number generator testutil handle.
rand_testutils_rng_t rand_testutils_rng_ctx;

// The OTTF overrides the default machine ecall exception handler to implement
// FreeRTOS context switching, required for supporting cooperative scheduling.
void ottf_machine_ecall_handler(void) {
  if (pxCurrentTCB != NULL) {
    // If the pointer to the current TCB is not NULL, we are operating in
    // concurrency mode. In this case, our default behavior is to assume a
    // context switch has been requested.
    vTaskSwitchContext();
    return;
  }
  LOG_ERROR(
      "OTTF currently only supports use of machine-mode ecall for FreeRTOS "
      "context switching.");
}

bool ottf_task_create(TaskFunction_t task_function, const char *task_name,
                      configSTACK_DEPTH_TYPE task_stack_depth,
                      uint32_t task_priority) {
  return xTaskCreate(/*pvTaskCode=*/task_function, /*pcName=*/task_name,
                     /*usStackDepth=*/task_stack_depth, /*pvParameters=*/NULL,
                     /*uxPriority=*/tskIDLE_PRIORITY + 1 + task_priority,
                     /*pxCreatedTask=*/NULL) == pdPASS
             ? true
             : false;
}

void ottf_task_yield(void) { taskYIELD(); }

void ottf_task_delete_self(void) { vTaskDelete(/*xTask=*/NULL); }

char *ottf_task_get_self_name(void) {
  return pcTaskGetName(/*xTaskToQuery=*/NULL);
}

static void report_test_status(bool result) {
  // Reinitialize UART before print any debug output if the test clobbered it.
  if (kDeviceType != kDeviceSimDV) {
    if (kOttfTestConfig.console.test_may_clobber) {
      ottf_console_init();
    }
    LOG_INFO("Finished %s", kOttfTestConfig.file);
  }

  coverage_send_buffer();
  test_status_set(result ? kTestStatusPassed : kTestStatusFailed);
}

// A wrapper function is required to enable `test_main()` and test teardown
// logic to be invoked as a FreeRTOS task. This wrapper can be used by tests
// that are run on bare-metal.
static void test_wrapper(void *task_parameters) {
  // Invoke test hooks that can be overridden by closed-source code.
  bool result = manufacturer_pre_test_hook();
  result = result && test_main();
  result = result && manufacturer_post_test_hook();
  report_test_status(result);
}

void _ottf_main(void) {
  test_status_set(kTestStatusInTest);

  // Initialize the console to enable logging for non-DV simulation platforms.
  if (kDeviceType != kDeviceSimDV) {
    ottf_console_init();
    LOG_INFO("Running %s", kOttfTestConfig.file);
  }

  // Initialize a global random number generator testutil context to provide
  // tests with a source of entropy for randomizing test behaviors.
  dif_rv_core_ibex_t rv_core_ibex;
  CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));
  rand_testutils_rng_ctx = rand_testutils_init(&rv_core_ibex);

  // Run the test.
  if (kOttfTestConfig.enable_concurrency) {
    // Run `test_main()` in a FreeRTOS task, allowing other FreeRTOS tasks to
    // be spawned, if requested in the main test task. Note, we spawn the main
    // test task at a priority level of 0.
    ottf_task_create(test_wrapper, "test_main", /*task_stack_depth=*/1024, 0);
    vTaskStartScheduler();
  } else {
    // Otherwise, launch `test_main()` on bare-metal.
    test_wrapper(NULL);
  }

  // Unreachable.
  CHECK(false);
}
