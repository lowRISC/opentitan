// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/pinmux_testutils.h"

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/testing/check.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define NUM_GPIO 32

void pinmux_testutils_init(dif_pinmux_t *pinmux) {
  // input: assign MIO0..MIO31 to GPIO0..GPIO31 (except UARTs)
  for (uint32_t index = 0; index < NUM_GPIO; index++) {
    dif_pinmux_index_t mio = kTopEarlgreyPinmuxInselIoa0 + index;
    if (mio == kTopEarlgreyPinmuxInselIoc3 ||
        mio == kTopEarlgreyPinmuxInselIoc8) {
      // Avoid causing glitches: Don't assign the UART pins to a GPIO.
      continue;
    } else {
      dif_pinmux_index_t gpio = kTopEarlgreyPinmuxPeripheralInGpioGpio0 + index;
      CHECK_DIF_OK(dif_pinmux_input_select(pinmux, gpio, mio));
    }
  }

  // output: assign GPIO0..GPIO31 to MIO0..MIO31 (except UARTs)
  for (uint32_t index = 0; index < NUM_GPIO; index++) {
    dif_pinmux_index_t mio = kTopEarlgreyPinmuxMioOutIoa0 + index;
    if (mio == kTopEarlgreyPinmuxMioOutIoc3 ||
        mio == kTopEarlgreyPinmuxMioOutIoc4 ||
        mio == kTopEarlgreyPinmuxMioOutIoc8 ||
        mio == kTopEarlgreyPinmuxMioOutIoc9) {
      // Avoid causing glitches: Don't assign the UART pins to a GPIO.
      continue;
    } else {
      dif_pinmux_index_t gpio = kTopEarlgreyPinmuxOutselGpioGpio0 + index;
      CHECK_DIF_OK(dif_pinmux_output_select(pinmux, mio, gpio));
    }
  }

  // Configure UART0 RX input to connect to MIO pad IOC3
  CHECK_DIF_OK(dif_pinmux_input_select(pinmux,
                                       kTopEarlgreyPinmuxPeripheralInUart0Rx,
                                       kTopEarlgreyPinmuxInselIoc3));
  CHECK_DIF_OK(dif_pinmux_output_select(pinmux, kTopEarlgreyPinmuxMioOutIoc3,
                                        kTopEarlgreyPinmuxOutselConstantHighZ));
  // Configure UART0 TX output to connect to MIO pad IOC4
  CHECK_DIF_OK(dif_pinmux_output_select(pinmux, kTopEarlgreyPinmuxMioOutIoc4,
                                        kTopEarlgreyPinmuxOutselUart0Tx));

#if !OT_IS_ENGLISH_BREAKFAST
  // Configure UART1 RX input to connect to MIO pad IOC8
  CHECK_DIF_OK(dif_pinmux_input_select(pinmux,
                                       kTopEarlgreyPinmuxPeripheralInUart1Rx,
                                       kTopEarlgreyPinmuxInselIoc8));
  CHECK_DIF_OK(dif_pinmux_output_select(pinmux, kTopEarlgreyPinmuxMioOutIoc8,
                                        kTopEarlgreyPinmuxOutselConstantHighZ));
  // Configure UART1 TX output to connect to MIO pad IOC9
  CHECK_DIF_OK(dif_pinmux_output_select(pinmux, kTopEarlgreyPinmuxMioOutIoc9,
                                        kTopEarlgreyPinmuxOutselUart1Tx));
#endif

  // Configure USBDEV SENSE outputs to be high-Z (IOR0, IOR1)
  CHECK_DIF_OK(dif_pinmux_output_select(pinmux, kTopEarlgreyPinmuxMioOutIor0,
                                        kTopEarlgreyPinmuxOutselConstantHighZ));
  CHECK_DIF_OK(dif_pinmux_output_select(pinmux, kTopEarlgreyPinmuxMioOutIor1,
                                        kTopEarlgreyPinmuxOutselConstantHighZ));
}
