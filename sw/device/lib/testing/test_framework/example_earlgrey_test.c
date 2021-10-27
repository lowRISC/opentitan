// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <sw/device/lib/testing/test_framework/ottf.h>

#include "sw/device/lib/dif/dif_rv_timer.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_framework/FreeRTOSConfig.h"
#include "sw/vendor/freertos_freertos_kernel/include/FreeRTOS.h"
#include "sw/vendor/freertos_freertos_kernel/include/task.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

const test_config_t kTestConfig = {
    .can_clobber_uart = false,
    .test_name = "ExampleTest",
};

// Currently, this test runs forever, but once test teardown logic has been
// implemented this example will be updated.
void test_main(void *result) {
  while (true) {
    // Calling pcTaskGetName() with NULL gets the name of the current task.
    LOG_INFO("(FreeRTOS Task): %s is running ...", pcTaskGetName(NULL));
  }

  *(bool *)result = true;

  // Calling vTaskDelete() with NULL triggers a task to delete itself.
  vTaskDelete(NULL);
}
