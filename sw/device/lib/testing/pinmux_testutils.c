// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/pinmux_testutils.h"

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/testing/test_framework/check.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

void pinmux_testutils_init(dif_pinmux_t *pinmux) {
  // Set up SW straps on IOC0-IOC2, for GPIOs 22-24
  CHECK_DIF_OK(dif_pinmux_input_select(pinmux,
                                       kTopEarlgreyPinmuxPeripheralInGpioGpio22,
                                       kTopEarlgreyPinmuxInselIoc0));
  CHECK_DIF_OK(dif_pinmux_input_select(pinmux,
                                       kTopEarlgreyPinmuxPeripheralInGpioGpio23,
                                       kTopEarlgreyPinmuxInselIoc1));
  CHECK_DIF_OK(dif_pinmux_input_select(pinmux,
                                       kTopEarlgreyPinmuxPeripheralInGpioGpio24,
                                       kTopEarlgreyPinmuxInselIoc2));
  CHECK_DIF_OK(dif_pinmux_output_select(pinmux, kTopEarlgreyPinmuxMioOutIoc0,
                                        kTopEarlgreyPinmuxOutselGpioGpio22));
  CHECK_DIF_OK(dif_pinmux_output_select(pinmux, kTopEarlgreyPinmuxMioOutIoc1,
                                        kTopEarlgreyPinmuxOutselGpioGpio23));
  CHECK_DIF_OK(dif_pinmux_output_select(pinmux, kTopEarlgreyPinmuxMioOutIoc2,
                                        kTopEarlgreyPinmuxOutselGpioGpio24));

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
  // Configure UART1 RX input to connect to MIO pad IOB4
  CHECK_DIF_OK(dif_pinmux_input_select(pinmux,
                                       kTopEarlgreyPinmuxPeripheralInUart1Rx,
                                       kTopEarlgreyPinmuxInselIob4));
  CHECK_DIF_OK(dif_pinmux_output_select(pinmux, kTopEarlgreyPinmuxMioOutIob4,
                                        kTopEarlgreyPinmuxOutselConstantHighZ));
  // Configure UART1 TX output to connect to MIO pad IOB5
  CHECK_DIF_OK(dif_pinmux_output_select(pinmux, kTopEarlgreyPinmuxMioOutIob5,
                                        kTopEarlgreyPinmuxOutselUart1Tx));
#endif

  // Configure USBDEV SENSE outputs to be high-Z (IOC7)
  CHECK_DIF_OK(dif_pinmux_output_select(pinmux, kTopEarlgreyPinmuxMioOutIoc7,
                                        kTopEarlgreyPinmuxOutselConstantHighZ));
}
