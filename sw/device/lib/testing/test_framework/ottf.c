// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/ottf.h"

#include <assert.h>
#include <stddef.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_framework/FreeRTOSConfig.h"
#include "sw/device/lib/testing/test_framework/test_coverage.h"
#include "sw/device/lib/testing/test_framework/test_status.h"
#include "sw/vendor/freertos_freertos_kernel/include/FreeRTOS.h"
#include "sw/vendor/freertos_freertos_kernel/include/queue.h"
#include "sw/vendor/freertos_freertos_kernel/include/task.h"

// TODO: make this toplevel agnostic.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Check layout of test configuration struct since OTTF ISR asm code requires a
// specific layout.
OT_ASSERT_MEMBER_OFFSET(test_config_t, enable_concurrency, 0);
OT_ASSERT_MEMBER_SIZE(test_config_t, enable_concurrency, 1);

// UART for communication with host.
static dif_uart_t uart0;

static void init_uart(void) {
  CHECK_DIF_OK(dif_uart_init(
      mmio_region_from_addr(TOP_EARLGREY_UART0_BASE_ADDR), &uart0));
  CHECK_DIF_OK(
      dif_uart_configure(&uart0, (dif_uart_config_t){
                                     .baudrate = kUartBaudrate,
                                     .clk_freq_hz = kClockFreqPeripheralHz,
                                     .parity_enable = kDifToggleDisabled,
                                     .parity = kDifUartParityEven,
                                 }));
  base_uart_stdout(&uart0);
}

static void report_test_status(bool result) {
  // Reinitialize UART before print any debug output if the test clobbered it.
  if (kDeviceType != kDeviceSimDV && kTestConfig.can_clobber_uart) {
    init_uart();
    test_coverage_send_buffer();
  }

  test_status_set(result ? kTestStatusPassed : kTestStatusFailed);
}

// A wrapper function is required to enable `test_main()` and test teardown
// logic to be invoked as a FreeRTOS task. This wrapper can be used by tests
// that are run on bare-metal.
static void test_wrapper(void *task_parameters) {
  bool result = test_main();
  report_test_status(result);
}

int main(int argc, char **argv) {
  test_status_set(kTestStatusInTest);

  // Initialize the UART to enable logging for non-DV simulation platforms.
  if (kDeviceType != kDeviceSimDV) {
    init_uart();
  }

  // Run the test.
  if (kTestConfig.enable_concurrency) {
    // Run `test_main()` in a FreeRTOS task, allowing other FreeRTOS tasks to
    // be spawned, if requested in the main test task.
    xTaskCreate(test_wrapper, "TestTask", configMINIMAL_STACK_SIZE, NULL,
                tskIDLE_PRIORITY + 1, NULL);
    vTaskStartScheduler();
  } else {
    // Otherwise, launch `test_main()` on bare-metal.
    test_wrapper(NULL);
  }

  // Unreachable code.
  return 1;
}
