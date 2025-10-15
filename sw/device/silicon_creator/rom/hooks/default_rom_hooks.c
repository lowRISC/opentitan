// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>

#include "hw/top/dt/dt_api.h"
#include "hw/top/dt/dt_gpio.h"
#include "hw/top/dt/dt_uart.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/drivers/pinmux.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/rom/rom_state.h"

#include "hw/top/otp_ctrl_regs.h"
#include "hw/top/rstmgr_regs.h"

// Default, ROM hooks for the OpenTitan Earlgrey ROM.
//
// See this repository's README.md and BUILD.bazel files to understand how to
// provide and use custom ROM hooks.

OT_WARN_UNUSED_RESULT
static rom_error_t rom_pinmux_init(void) {
  uint32_t bootstrap_dis =
      otp_read32(OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_BOOTSTRAP_DIS_OFFSET);
  if (launder32(bootstrap_dis) != kHardenedBoolTrue) {
    HARDENED_CHECK_NE(bootstrap_dis, kHardenedBoolTrue);

    // Configure the pads before the pinmux matrix to avoid
    // "undesired electrical behavior and/or contention at the pads".
    HARDENED_RETURN_IF_ERROR(pinmux_enable_pull_down(kDtPadIoc0));
    HARDENED_RETURN_IF_ERROR(pinmux_enable_pull_down(kDtPadIoc1));
    HARDENED_RETURN_IF_ERROR(pinmux_enable_pull_down(kDtPadIoc2));

    // Set up SW straps on IOC0-IOC2, for GPIOs 22-24.
    HARDENED_RETURN_IF_ERROR(
        pinmux_connect(dt_gpio_periph_io(kDtGpio, kDtGpioPeriphIoGpio22),
                       kDtPadIoc0, kDtPeriphIoDirIn));
    HARDENED_RETURN_IF_ERROR(
        pinmux_connect(dt_gpio_periph_io(kDtGpio, kDtGpioPeriphIoGpio23),
                       kDtPadIoc1, kDtPeriphIoDirIn));
    HARDENED_RETURN_IF_ERROR(
        pinmux_connect(dt_gpio_periph_io(kDtGpio, kDtGpioPeriphIoGpio24),
                       kDtPadIoc2, kDtPeriphIoDirIn));
  }

  // Pull the UART_RX line high (idle state for UART).  This prevents a
  // floating UART_RX from incorrectly triggering serial break.
  HARDENED_RETURN_IF_ERROR(pinmux_enable_pull_up(kDtPadIoc3));

  // Connect the UART0 Rx pad to the UART0 Rx input.
  HARDENED_RETURN_IF_ERROR(
      pinmux_connect(dt_uart_periph_io(kDtUart0, kDtUartPeriphIoRx), kDtPadIoc3,
                     kDtPeriphIoDirIn));

  // Connect the UART0 Tx output to the UART0 Tx pad.
  HARDENED_RETURN_IF_ERROR(
      pinmux_connect(dt_uart_periph_io(kDtUart0, kDtUartPeriphIoTx), kDtPadIoc4,
                     kDtPeriphIoDirOut));

  return kErrorOk;
}

OT_WARN_UNUSED_RESULT rom_error_t rom_init_pre_hook(void *arg) {
  uint32_t reset_reasons = rstmgr_reason_get();
  if (reset_reasons != (1U << RSTMGR_RESET_INFO_LOW_POWER_EXIT_BIT)) {
    // Initialize pinmux configuration so we can use the UART, (except if waking
    // up from low power, as the pinmux will in such case have retained its
    // previous configuration.)
    HARDENED_RETURN_IF_ERROR(rom_pinmux_init());
  }

  return kErrorOk;
}
ROM_STATE_PRE_HOOK(kRomStateInit, rom_init_pre_hook);
