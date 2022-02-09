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
#include "sw/device/silicon_creator/lib/manifest.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

/**
 * This symbol is defined in `sw/device/lib/testing/test_rom/test_rom.ld`,
 * and describes the location of the flash header.
 *
 * The actual contents are not defined by the ROM, but rather
 * by the flash binary: see `sw/device/lib/testing/test_framework/ottf.ld`
 * for that.
 */
extern manifest_t _manifest;

/**
 * Type alias for the OTTF entry point.
 *
 * The entry point address obtained from the OTTF manifest must be cast to a
 * pointer to this type before being called.
 */
typedef void ottf_entry(void);

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

  // TODO(lowrisc/opentitan:#10712): setup Ibex address translation

  // Jump to the OTTF in flash. Within the flash binary, it is the responsibily
  // of the OTTF to set up its own stack, and to never return.
  uintptr_t manifest_entry_point = _manifest.entry_point;
  LOG_INFO("Test ROM complete, jumping to flash!");
  ((ottf_entry *)manifest_entry_point)();

  // If the flash image returns, we should abort anyway.
  abort();
}
