// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <sw/device/lib/testing/test_framework/ottf.h>

#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/FreeRTOSConfig.h"
#include "sw/vendor/freertos_freertos_kernel/include/FreeRTOS.h"
#include "sw/vendor/freertos_freertos_kernel/include/task.h"

const test_config_t kTestConfig = {
    .can_clobber_uart = false,
};

bool test_main(void) {
  // Calling pcTaskGetName() with NULL gets the name of the current task.
  LOG_INFO("Running %s in FreeRTOS ...", pcTaskGetName(NULL));
  return true;
}
