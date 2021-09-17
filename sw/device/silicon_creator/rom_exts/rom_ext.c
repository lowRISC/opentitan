// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom_exts/rom_ext.h"

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/stdasm.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/epmp_test_unlock.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

// Secure MMIO context.
//
// This is placed at a fixed location in memory within the .static_critical
// section. It will be populated by the mask ROM before the jump to ROM_EXT.
__attribute__((section(".static_critical.sec_mmio_ctx")))  //
volatile sec_mmio_ctx_t sec_mmio_ctx;

static dif_uart_t uart;

int main(int argc, char *argv[]);

// TODO - need to decide what happens to the peripherals during the
//        Mask ROM to ROM_EXT handover (for example, does UART need
//        re-configuring, etc...). It is possible that the signature of
//        this function will change to pass the relevant information from
//        the Mask ROM.
void rom_ext_boot(void) {
  // Unlock the DV address space so that test results can be written out.
  // TODO: move to a test library.
  if (!epmp_unlock_test_status(NULL)) {
    abort();
  }

  dif_result_t init_result =
      dif_uart_init(mmio_region_from_addr(TOP_EARLGREY_UART0_BASE_ADDR), &uart);

  if (init_result != kDifOk) {
    abort();
  }

  dif_uart_config_result_t config_result =
      dif_uart_configure(&uart, (dif_uart_config_t){
                                    .baudrate = kUartBaudrate,
                                    .clk_freq_hz = kClockFreqPeripheralHz,
                                    .parity_enable = kDifToggleDisabled,
                                    .parity = kDifUartParityEven,
                                });

  if (config_result != kDifUartConfigOk) {
    abort();
  }

  base_uart_stdout(&uart);

  base_printf("Hello World!\n");

  // TODO - there might be another level before jumping into main.
  (void)main(0, NULL);

  // TODO - is this a correct way of handling the "return"?
  while (true) {
    wait_for_interrupt();
  }
}
