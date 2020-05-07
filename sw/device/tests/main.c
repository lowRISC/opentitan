// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/log.h"
#include "sw/device/lib/base/print.h"
#include "sw/device/lib/testing/test_main.h"
#include "sw/device/lib/testing/test_status.h"
#include "sw/device/lib/uart.h"

int main(int argc, char **argv) {
  test_status_set(kTestStatusInTest);

  // Initialize the UART to enable logging for non-DV simulation platforms.
  if (kDeviceType != kDeviceSimDV) {
    uart_init(kUartBaudrate);
    base_set_stdout(uart_stdout);
  }

  // Run the SW test which is fully contained within `test_main()`.
  bool result = test_main();
  test_status_set(result ? kTestStatusPassed : kTestStatusFailed);

  // Unreachable code.
  return 1;
}
