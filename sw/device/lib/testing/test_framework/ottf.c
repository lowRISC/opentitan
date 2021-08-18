// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/ottf.h"

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/dif/dif_uart.h"
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

// UART for communication with host.
static dif_uart_t uart0;

static void init_uart(void) {
  CHECK(dif_uart_init(mmio_region_from_addr(TOP_EARLGREY_UART0_BASE_ADDR),
                      &uart0) == kDifOk,
        "failed to init UART");
  CHECK(dif_uart_configure(&uart0,
                           (dif_uart_config_t){
                               .baudrate = kUartBaudrate,
                               .clk_freq_hz = kClockFreqPeripheralHz,
                               .parity_enable = kDifToggleDisabled,
                               .parity = kDifUartParityEven,
                           }) == kDifUartConfigOk,
        "failed to configure UART");
  base_uart_stdout(&uart0);
}

int main(int argc, char **argv) {
  test_status_set(kTestStatusInTest);

  // Initialize the UART to enable logging for non-DV simulation platforms.
  if (kDeviceType != kDeviceSimDV) {
    init_uart();
  }

  // Run the test, which is contained within `test_main()`, as a FreeRTOS task.
  bool result = false;
  LOG_INFO("Starting test (%s) in a FreeRTOS task ...", kTestConfig.test_name);
  TaskHandle_t test_task_handle = NULL;
  xTaskCreate(test_main, kTestConfig.test_name, configMINIMAL_STACK_SIZE,
              &result, tskIDLE_PRIORITY + 1, &test_task_handle);
  vTaskStartScheduler();

  // Must happen before any debug output.
  if (kTestConfig.can_clobber_uart) {
    init_uart();
  }

  test_coverage_send_buffer();
  test_status_set(result ? kTestStatusPassed : kTestStatusFailed);

  // Unreachable code.
  return 1;
}
