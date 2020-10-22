// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/rom_exts/rom_ext.h"

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/stdasm.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/print.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

static dif_uart_t uart;

// TODO - need to decide what happens to the peripherals during the
//        Mask ROM to ROM_EXT handover (for example, does UART need
//        re-configuring, etc...). It is possible that the signature of
//        this function will change to pass the relevant information from
//        the Mask ROM.
void rom_ext_boot(void) {
  dif_uart_result_t init_result = dif_uart_init(
      (dif_uart_params_t){
          .base_addr = mmio_region_from_addr(TOP_EARLGREY_UART_BASE_ADDR),
      },
      &uart);

  if (init_result != kDifUartOk) {
    abort();
  }

  dif_uart_config_result_t config_result =
      dif_uart_configure(&uart, (dif_uart_config_t){
                                    .baudrate = kUartBaudrate,
                                    .clk_freq_hz = kClockFreqPeripheralHz,
                                    .parity_enable = kDifUartToggleDisabled,
                                    .parity = kDifUartParityEven,
                                });

  if (config_result != kDifUartConfigOk) {
    abort();
  }

  base_uart_stdout(&uart);

  base_printf("Hello World!\n");

  // TODO - is this a correct way of handling the "return"?
  while (true) {
    wait_for_interrupt();
  }
}
