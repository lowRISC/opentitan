// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/flash_ctrl.h"
#include "sw/device/lib/ibex_peri.h"
#include "sw/device/lib/pinmux.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_framework/test_status.h"
#include "sw/device/lib/testing/test_rom/bootstrap.h"
#include "sw/device/lib/testing/test_rom/chip_info.h"  // Generated.

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

/**
 * This symbol is defined in `sw/device/lib/testing/test_rom/test_rom.ld`,
 * and describes the location of the flash header.
 *
 * The actual contents are not defined by the ROM, but rather
 * by the flash binary: see `sw/device/lib/testing/test_framework/ottf.ld`
 * for that.
 */
extern struct { void (*entry)(void); } _flash_header;
extern uint32_t _vflash_size;
extern uint32_t _flash_start;

static dif_uart_t uart0;

void _boot_start(void) {
  test_status_set(kTestStatusInBootRom);
  pinmux_init();
  flash_init();
  while (flash_get_init_status())
    ;

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

  LOG_INFO("%s", chip_info);

  int bootstrap_err = bootstrap();
  if (bootstrap_err != 0) {
    LOG_ERROR("Bootstrap failed with status code: %d", bootstrap_err);
    // Currently the only way to recover is by a hard reset.
    test_status_set(kTestStatusFailed);
  }

  // Simple transalation on flash
  uint32_t src_addr = (uint32_t)&_flash_header;
  uint32_t size = (uint32_t)&_vflash_size;
  uint32_t dst_addr = (uint32_t)&_flash_start;

  init_translation(src_addr, size, dst_addr);

  LOG_INFO("Boot ROM initialisation has completed, jump into flash!");

  // Jump into flash. At this point, the contents of the flash binary have been
  // verified, and we can transfer control directly to it. It is the
  // flash binary's responsibily to set up its own stack, and to never
  // return.
  _flash_header.entry();

  // If the flash image returns, we should abort anyway.
  abort();
}
