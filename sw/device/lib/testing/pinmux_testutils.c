// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/pinmux_testutils.h"

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_gpio.h"
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
  // Enable pull-ups on UART0 RX
  // Pull-ups are available only on certain platforms.
  if (kDeviceType == kDeviceSimDV) {
    dif_pinmux_pad_attr_t out_attr;
    dif_pinmux_pad_attr_t in_attr = {
        .slew_rate = 0,
        .drive_strength = 0,
        .flags = kDifPinmuxPadAttrPullResistorEnable |
                 kDifPinmuxPadAttrPullResistorUp};

    CHECK_DIF_OK(dif_pinmux_pad_write_attrs(pinmux, kTopEarlgreyMuxedPadsIoc3,
                                            kDifPinmuxPadKindMio, in_attr,
                                            &out_attr));
  };

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

// Mapping of Chip IOs to the GPIO peripheral.
//
// Depending on the simulation platform, there may be a limitation to how chip
// IOs are allocated to the GPIO peripheral, even for testing. The DV testbench
// does not have this limitation, and is able to allocate as many chip IOs as
// the number of GPIOs supported by the peripheral. At this time, these pin
// assignments matches DV (see `hw/top_earlgrey/dv/env/chip_if.sv`).
//
// The pinout spreadsheet allocates fewer pins to GPIOs than what the GPIO IP
// supports. This oversubscription is intentional to maximize testing.
const dif_pinmux_index_t kPinmuxTestutilsGpioInselPins[kDifGpioNumPins] = {
    kTopEarlgreyPinmuxInselIoa0,  kTopEarlgreyPinmuxInselIoa1,
    kTopEarlgreyPinmuxInselIoa2,  kTopEarlgreyPinmuxInselIoa3,
    kTopEarlgreyPinmuxInselIoa4,  kTopEarlgreyPinmuxInselIoa5,
    kTopEarlgreyPinmuxInselIoa6,  kTopEarlgreyPinmuxInselIoa7,
    kTopEarlgreyPinmuxInselIoa8,  kTopEarlgreyPinmuxInselIob6,
    kTopEarlgreyPinmuxInselIob7,  kTopEarlgreyPinmuxInselIob8,
    kTopEarlgreyPinmuxInselIob9,  kTopEarlgreyPinmuxInselIob10,
    kTopEarlgreyPinmuxInselIob11, kTopEarlgreyPinmuxInselIob12,
    kTopEarlgreyPinmuxInselIoc9,  kTopEarlgreyPinmuxInselIoc10,
    kTopEarlgreyPinmuxInselIoc11, kTopEarlgreyPinmuxInselIoc12,
    kTopEarlgreyPinmuxInselIor0,  kTopEarlgreyPinmuxInselIor1,
    kTopEarlgreyPinmuxInselIor2,  kTopEarlgreyPinmuxInselIor3,
    kTopEarlgreyPinmuxInselIor4,  kTopEarlgreyPinmuxInselIor5,
    kTopEarlgreyPinmuxInselIor6,  kTopEarlgreyPinmuxInselIor7,
    kTopEarlgreyPinmuxInselIor10, kTopEarlgreyPinmuxInselIor11,
    kTopEarlgreyPinmuxInselIor12, kTopEarlgreyPinmuxInselIor13};

const dif_pinmux_index_t kPinmuxTestutilsGpioMioOutPins[kDifGpioNumPins] = {
    kTopEarlgreyPinmuxMioOutIoa0,  kTopEarlgreyPinmuxMioOutIoa1,
    kTopEarlgreyPinmuxMioOutIoa2,  kTopEarlgreyPinmuxMioOutIoa3,
    kTopEarlgreyPinmuxMioOutIoa4,  kTopEarlgreyPinmuxMioOutIoa5,
    kTopEarlgreyPinmuxMioOutIoa6,  kTopEarlgreyPinmuxMioOutIoa7,
    kTopEarlgreyPinmuxMioOutIoa8,  kTopEarlgreyPinmuxMioOutIob6,
    kTopEarlgreyPinmuxMioOutIob7,  kTopEarlgreyPinmuxMioOutIob8,
    kTopEarlgreyPinmuxMioOutIob9,  kTopEarlgreyPinmuxMioOutIob10,
    kTopEarlgreyPinmuxMioOutIob11, kTopEarlgreyPinmuxMioOutIob12,
    kTopEarlgreyPinmuxMioOutIoc9,  kTopEarlgreyPinmuxMioOutIoc10,
    kTopEarlgreyPinmuxMioOutIoc11, kTopEarlgreyPinmuxMioOutIoc12,
    kTopEarlgreyPinmuxMioOutIor0,  kTopEarlgreyPinmuxMioOutIor1,
    kTopEarlgreyPinmuxMioOutIor2,  kTopEarlgreyPinmuxMioOutIor3,
    kTopEarlgreyPinmuxMioOutIor4,  kTopEarlgreyPinmuxMioOutIor5,
    kTopEarlgreyPinmuxMioOutIor6,  kTopEarlgreyPinmuxMioOutIor7,
    kTopEarlgreyPinmuxMioOutIor10, kTopEarlgreyPinmuxMioOutIor11,
    kTopEarlgreyPinmuxMioOutIor12, kTopEarlgreyPinmuxMioOutIor13};

uint32_t pinmux_testutils_get_testable_gpios_mask(void) {
  if (kDeviceType == kDeviceFpgaCw310) {
    // Only IOA2 to IOA8 are available for use as GPIOs.
    return 0x1fc;
  } else {
    return 0xffffffff;
  }
}
