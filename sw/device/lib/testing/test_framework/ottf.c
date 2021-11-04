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

static void freertos_test_task(void *task_parameters) {
  bool result = test_main();

  // Must happen before any debug output.
  if (kTestConfig.can_clobber_uart) {
    init_uart();
  }

  test_coverage_send_buffer();
  test_status_set(result ? kTestStatusPassed : kTestStatusFailed);
}

int main(int argc, char **argv) {
  test_status_set(kTestStatusInTest);

  // Initialize the UART to enable logging for non-DV simulation platforms.
  if (kDeviceType != kDeviceSimDV) {
    init_uart();
  }

  // Run the test, which is contained within `test_main()`, as a FreeRTOS task.
  xTaskCreate(freertos_test_task, "OTTFTestTask", configMINIMAL_STACK_SIZE,
              NULL, tskIDLE_PRIORITY + 1, NULL);
  vTaskStartScheduler();

  // Unreachable code.
  return 1;
}
