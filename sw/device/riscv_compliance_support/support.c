// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stddef.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_status.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

// These symbopls are provided by the riscv-compliance libraries.
extern void run_rvc_test(void);
extern volatile uint32_t begin_signature[];
extern volatile uint32_t end_signature[];

static dif_uart_t uart0;

int opentitan_compliance_main(int argc, char **argv) {
  CHECK(
      dif_uart_init(
          (dif_uart_params_t){
              .base_addr = mmio_region_from_addr(TOP_EARLGREY_UART0_BASE_ADDR),
          },
          &uart0) == kDifUartOk,
      "failed to init UART");
  CHECK(dif_uart_configure(&uart0,
                           (dif_uart_config_t){
                               .baudrate = kUartBaudrate,
                               .clk_freq_hz = kClockFreqPeripheralHz,
                               .parity_enable = kDifUartToggleDisabled,
                               .parity = kDifUartParityEven,
                           }) == kDifUartConfigOk,
        "failed to configure UART");
  base_uart_stdout(&uart0);

  run_rvc_test();

  ptrdiff_t size = end_signature - begin_signature;
  for (int i = 0; i < size; ++i) {
    base_printf("SIG: %08x\r\n", begin_signature[i]);
  }

  // Above values are checked for correctness externally post-simulation.
  test_status_set(kTestStatusPassed);

  // Unreachable code.
  return 0;
}
