// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/pinmux.h"

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/runtime/hart.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define PINMUX0_BASE_ADDR TOP_EARLGREY_PINMUX_AON_BASE_ADDR

#define NUM_GPIO 32

/**
 * Checks that the given DIF call returns kDifOk. If the DIF call returns a
 * different dif_result_t value (defined in sw/device/lib/dif/dif_base.h), this
 * function aborts.
 *
 * A similar macro performs logging, but this is often not available during
 * pinmux initialization, so this one does not.
 *
 * @param dif_call DIF call to invoke and check its return value.
 * fails.
 */
#define CHECK_PINMUX_DIF_OK(dif_call)   \
  do {                                  \
    dif_result_t dif_result = dif_call; \
    if (dif_result != kDifOk) {         \
      abort();                          \
    }                                   \
  } while (false)

void pinmux_init(void) {
  dif_pinmux_t pinmux;
  mmio_region_t pinmux_base_addr = mmio_region_from_addr(PINMUX0_BASE_ADDR);
  CHECK_PINMUX_DIF_OK(dif_pinmux_init(pinmux_base_addr, &pinmux));
  // TODO: This hardcoded configuration is temporary and needs to be
  // replaced by proper initialization code

  // input: assign MIO0..MIO31 to GPIO0..GPIO31 (except UARTs)
  for (uint32_t index = 0; index < NUM_GPIO; index++) {
    dif_pinmux_index_t mio = kTopEarlgreyPinmuxInselIoa0 + index;
    if (mio == kTopEarlgreyPinmuxInselIoc3 ||
        mio == kTopEarlgreyPinmuxInselIoc8) {
      // Avoid causing glitches: Don't assign the UART pins to a GPIO.
      continue;
    } else {
      dif_pinmux_index_t gpio = kTopEarlgreyPinmuxPeripheralInGpioGpio0 + index;
      CHECK_PINMUX_DIF_OK(dif_pinmux_input_select(&pinmux, gpio, mio));
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
      CHECK_PINMUX_DIF_OK(dif_pinmux_output_select(&pinmux, mio, gpio));
    }
  }

  // Configure UART0 RX input to connect to MIO pad IOC3
  CHECK_PINMUX_DIF_OK(
      dif_pinmux_input_select(&pinmux, kTopEarlgreyPinmuxPeripheralInUart0Rx,
                              kTopEarlgreyPinmuxInselIoc3));
  CHECK_PINMUX_DIF_OK(
      dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIoc3,
                               kTopEarlgreyPinmuxOutselConstantHighZ));
  // Configure UART0 TX output to connect to MIO pad IOC4
  CHECK_PINMUX_DIF_OK(dif_pinmux_output_select(
      &pinmux, kTopEarlgreyPinmuxMioOutIoc4, kTopEarlgreyPinmuxOutselUart0Tx));

#if !OT_IS_ENGLISH_BREAKFAST
  // Configure UART1 RX input to connect to MIO pad IOC8
  CHECK_PINMUX_DIF_OK(
      dif_pinmux_input_select(&pinmux, kTopEarlgreyPinmuxPeripheralInUart1Rx,
                              kTopEarlgreyPinmuxInselIoc8));
  CHECK_PINMUX_DIF_OK(
      dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIoc8,
                               kTopEarlgreyPinmuxOutselConstantHighZ));
  // Configure UART1 TX output to connect to MIO pad IOC9
  CHECK_PINMUX_DIF_OK(dif_pinmux_output_select(
      &pinmux, kTopEarlgreyPinmuxMioOutIoc9, kTopEarlgreyPinmuxOutselUart1Tx));
#endif

  // Configure USBDEV SENSE outputs to be high-Z (IOR0, IOR1)
  CHECK_PINMUX_DIF_OK(
      dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIor0,
                               kTopEarlgreyPinmuxOutselConstantHighZ));
  CHECK_PINMUX_DIF_OK(
      dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIor1,
                               kTopEarlgreyPinmuxOutselConstantHighZ));
}
