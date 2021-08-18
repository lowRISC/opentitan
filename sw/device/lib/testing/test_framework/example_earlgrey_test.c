// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <sw/device/lib/testing/test_framework/ottf.h>

#include "sw/device/lib/dif/dif_rv_timer.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/vendor/freertos_freertos_kernel/include/FreeRTOS.h"
#include "sw/vendor/freertos_freertos_kernel/include/task.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

const test_config_t kTestConfig = {
    .can_clobber_uart = false,
    .test_name = "ExampleTest",
};

// This example test just queries the RV Timer count and logs it over UART.
// Currently, this test runs forever, but once test teardown logic has been
// implemented this example will be updated.
void test_main(void *result) {
  mmio_region_t timer_reg =
      mmio_region_from_addr(TOP_EARLGREY_RV_TIMER_BASE_ADDR);
  dif_rv_timer_t timer = {
      .base_addr = timer_reg,
      {.hart_count = 1, .comparator_count = 1},
  };
  uint64_t current_time;
  const uint32_t kHart = (uint32_t)kTopEarlgreyPlicTargetIbex0;

  while (true) {
    CHECK(dif_rv_timer_counter_read(&timer, kHart, &current_time) ==
          kDifRvTimerOk);
    LOG_INFO("(FreeRTOS Task) Current Time: %u", (uint32_t)current_time);
  }

  *(bool *)result = true;

  // Calling vTaskDelete() with NULL triggers a task to delete itself.
  vTaskDelete(NULL);
}
