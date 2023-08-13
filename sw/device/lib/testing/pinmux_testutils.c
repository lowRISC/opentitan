// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/pinmux_testutils.h"

#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/ip/base/dif/dif_base.h"
#include "sw/ip/gpio/dif/dif_gpio.h"
#include "sw/ip/pinmux/dif/dif_pinmux.h"
#include "sw/lib/sw/device/arch/device.h"
#include "sw/lib/sw/device/base/macros.h"
#include "sw/lib/sw/device/base/status.h"
#include "sw/lib/sw/device/runtime/hart.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"

void pinmux_testutils_init(dif_pinmux_t *pinmux) {
  // Set up SW straps on IOC0-IOC2, for GPIOs 22-24
  CHECK_DIF_OK(dif_pinmux_input_select(
      pinmux, kTopDarjeelingPinmuxPeripheralInGpioGpio22,
      kTopDarjeelingPinmuxInselIoc0));
  CHECK_DIF_OK(dif_pinmux_input_select(
      pinmux, kTopDarjeelingPinmuxPeripheralInGpioGpio23,
      kTopDarjeelingPinmuxInselIoc1));
  CHECK_DIF_OK(dif_pinmux_input_select(
      pinmux, kTopDarjeelingPinmuxPeripheralInGpioGpio24,
      kTopDarjeelingPinmuxInselIoc2));

  // Configure UART0 RX input to connect to MIO pad IOC3
  CHECK_DIF_OK(dif_pinmux_input_select(pinmux,
                                       kTopDarjeelingPinmuxPeripheralInUart0Rx,
                                       kTopDarjeelingPinmuxInselIoc3));
  CHECK_DIF_OK(
      dif_pinmux_output_select(pinmux, kTopDarjeelingPinmuxMioOutIoc3,
                               kTopDarjeelingPinmuxOutselConstantHighZ));
  // Configure UART0 TX output to connect to MIO pad IOC4
  CHECK_DIF_OK(dif_pinmux_output_select(pinmux, kTopDarjeelingPinmuxMioOutIoc4,
                                        kTopDarjeelingPinmuxOutselUart0Tx));

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

    CHECK_DIF_OK(dif_pinmux_pad_write_attrs(pinmux, kTopDarjeelingMuxedPadsIoc3,
                                            kDifPinmuxPadKindMio, in_attr,
                                            &out_attr));
  };

  // Configure UART1 RX input to connect to MIO pad IOB4
  CHECK_DIF_OK(dif_pinmux_input_select(pinmux,
                                       kTopDarjeelingPinmuxPeripheralInUart1Rx,
                                       kTopDarjeelingPinmuxInselIob4));
  CHECK_DIF_OK(
      dif_pinmux_output_select(pinmux, kTopDarjeelingPinmuxMioOutIob4,
                               kTopDarjeelingPinmuxOutselConstantHighZ));
  // Configure UART1 TX output to connect to MIO pad IOB5
  CHECK_DIF_OK(dif_pinmux_output_select(pinmux, kTopDarjeelingPinmuxMioOutIob5,
                                        kTopDarjeelingPinmuxOutselUart1Tx));

  // Configure a higher drive strength for the USB_P and USB_N pads because we
  // must the pad drivers must be capable of overpowering the 'pull' signal
  // strength of the internal pull ups in the differential receiver.
  //
  // 'pull' strength is required because at the host end of the USB, there
  // are 'weak' pull downs, allowing it to detect device presence when it
  // applies its pull up.
  //    strong PAD driver > internal pull up > weak pull down at host
  //
  // Normally the pull up on USB_P will be asserted, but we may be employing
  // 'pin flipping' and instead choose to apply the _N pull up.
  if (kDeviceType == kDeviceSimDV) {
    dif_pinmux_pad_attr_t out_attr;
    dif_pinmux_pad_attr_t in_attr = {
        .slew_rate = 0, .drive_strength = 1, .flags = 0};

    CHECK_DIF_OK(
        dif_pinmux_pad_write_attrs(pinmux, kTopDarjeelingDirectPadsUsbdevUsbDp,
                                   kDifPinmuxPadKindDio, in_attr, &out_attr));
    CHECK_DIF_OK(
        dif_pinmux_pad_write_attrs(pinmux, kTopDarjeelingDirectPadsUsbdevUsbDn,
                                   kDifPinmuxPadKindDio, in_attr, &out_attr));
  }
#endif

  // Configure USBDEV SENSE outputs to be high-Z (IOC7)
  CHECK_DIF_OK(
      dif_pinmux_output_select(pinmux, kTopDarjeelingPinmuxMioOutIoc7,
                               kTopDarjeelingPinmuxOutselConstantHighZ));
}

// Mapping of Chip IOs to the GPIO peripheral.
//
// Depending on the simulation platform, there may be a limitation to how chip
// IOs are allocated to the GPIO peripheral, even for testing. The DV testbench
// does not have this limitation, and is able to allocate as many chip IOs as
// the number of GPIOs supported by the peripheral. At this time, these pin
// assignments matches DV (see `hw/top_darjeeling/dv/env/chip_if.sv`).
//
// The pinout spreadsheet allocates fewer pins to GPIOs than what the GPIO IP
// supports. This oversubscription is intentional to maximize testing.
const dif_pinmux_index_t kPinmuxTestutilsGpioInselPins[kDifGpioNumPins] = {
    kTopDarjeelingPinmuxInselIoa0,  kTopDarjeelingPinmuxInselIoa1,
    kTopDarjeelingPinmuxInselIoa2,  kTopDarjeelingPinmuxInselIoa3,
    kTopDarjeelingPinmuxInselIoa4,  kTopDarjeelingPinmuxInselIoa5,
    kTopDarjeelingPinmuxInselIoa6,  kTopDarjeelingPinmuxInselIoa7,
    kTopDarjeelingPinmuxInselIoa8,  kTopDarjeelingPinmuxInselIob6,
    kTopDarjeelingPinmuxInselIob7,  kTopDarjeelingPinmuxInselIob8,
    kTopDarjeelingPinmuxInselIob9,  kTopDarjeelingPinmuxInselIob10,
    kTopDarjeelingPinmuxInselIob11, kTopDarjeelingPinmuxInselIob12,
    kTopDarjeelingPinmuxInselIoc9,  kTopDarjeelingPinmuxInselIoc10,
    kTopDarjeelingPinmuxInselIoc11, kTopDarjeelingPinmuxInselIoc12,
    kTopDarjeelingPinmuxInselIor0,  kTopDarjeelingPinmuxInselIor1,
    kTopDarjeelingPinmuxInselIor2,  kTopDarjeelingPinmuxInselIor3,
    kTopDarjeelingPinmuxInselIor4,  kTopDarjeelingPinmuxInselIor5,
    kTopDarjeelingPinmuxInselIor6,  kTopDarjeelingPinmuxInselIor7,
    kTopDarjeelingPinmuxInselIor10, kTopDarjeelingPinmuxInselIor11,
    kTopDarjeelingPinmuxInselIor12, kTopDarjeelingPinmuxInselIor13};

const dif_pinmux_index_t kPinmuxTestutilsGpioMioOutPins[kDifGpioNumPins] = {
    kTopDarjeelingPinmuxMioOutIoa0,  kTopDarjeelingPinmuxMioOutIoa1,
    kTopDarjeelingPinmuxMioOutIoa2,  kTopDarjeelingPinmuxMioOutIoa3,
    kTopDarjeelingPinmuxMioOutIoa4,  kTopDarjeelingPinmuxMioOutIoa5,
    kTopDarjeelingPinmuxMioOutIoa6,  kTopDarjeelingPinmuxMioOutIoa7,
    kTopDarjeelingPinmuxMioOutIoa8,  kTopDarjeelingPinmuxMioOutIob6,
    kTopDarjeelingPinmuxMioOutIob7,  kTopDarjeelingPinmuxMioOutIob8,
    kTopDarjeelingPinmuxMioOutIob9,  kTopDarjeelingPinmuxMioOutIob10,
    kTopDarjeelingPinmuxMioOutIob11, kTopDarjeelingPinmuxMioOutIob12,
    kTopDarjeelingPinmuxMioOutIoc9,  kTopDarjeelingPinmuxMioOutIoc10,
    kTopDarjeelingPinmuxMioOutIoc11, kTopDarjeelingPinmuxMioOutIoc12,
    kTopDarjeelingPinmuxMioOutIor0,  kTopDarjeelingPinmuxMioOutIor1,
    kTopDarjeelingPinmuxMioOutIor2,  kTopDarjeelingPinmuxMioOutIor3,
    kTopDarjeelingPinmuxMioOutIor4,  kTopDarjeelingPinmuxMioOutIor5,
    kTopDarjeelingPinmuxMioOutIor6,  kTopDarjeelingPinmuxMioOutIor7,
    kTopDarjeelingPinmuxMioOutIor10, kTopDarjeelingPinmuxMioOutIor11,
    kTopDarjeelingPinmuxMioOutIor12, kTopDarjeelingPinmuxMioOutIor13};

uint32_t pinmux_testutils_get_testable_gpios_mask(void) {
  if (kDeviceType == kDeviceFpgaCw310) {
    // Only IOR6, IOR7, and IOR10 to IOR13 are available for use as GPIOs.
    return 0xfc000000;
  } else {
    return 0xffffffff;
  }
}

uint32_t pinmux_testutils_read_strap_pin(dif_pinmux_t *pinmux, dif_gpio_t *gpio,
                                         dif_gpio_pin_t io,
                                         top_darjeeling_muxed_pads_t pad) {
  // Turn off the pull enable on the pad and read the IO.
  dif_pinmux_pad_attr_t attr = {.flags = 0};
  dif_pinmux_pad_attr_t attr_out;
  CHECK_DIF_OK(dif_pinmux_pad_write_attrs(pinmux, pad, kDifPinmuxPadKindMio,
                                          attr, &attr_out));
  bool state;
  // The value read is unmodified by the internal pull resistors and represents
  // the upper bit of the 4 possible states [Strong0, Weak0, Weak1,
  // Strong1].
  CHECK_DIF_OK(dif_gpio_read(gpio, io, &state));
  uint32_t result = state ? 2 : 0;

  // Based on the previous read, enable the opposite pull resistor.  If the
  // external signal is weak, the internal pull resistor will win; if the
  // external signal is strong, the external value will win.
  attr.flags = kDifPinmuxPadAttrPullResistorEnable |
               (state ? 0 : kDifPinmuxPadAttrPullResistorUp);
  CHECK_DIF_OK(dif_pinmux_pad_write_attrs(pinmux, pad, kDifPinmuxPadKindMio,
                                          attr, &attr_out));
  // Combine the result of the contest between the external signal in internal
  // pull resistors.  This represents the lower bit of the 4 possible states.
  CHECK_DIF_OK(dif_gpio_read(gpio, io, &state));
  result += state ? 1 : 0;
  return result;
}

uint32_t pinmux_testutils_read_straps(dif_pinmux_t *pinmux, dif_gpio_t *gpio) {
  uint32_t strap = 0;
  strap |= pinmux_testutils_read_strap_pin(pinmux, gpio, 22,
                                           kTopDarjeelingMuxedPadsIoc0);
  strap |= pinmux_testutils_read_strap_pin(pinmux, gpio, 23,
                                           kTopDarjeelingMuxedPadsIoc1)
           << 2;
  strap |= pinmux_testutils_read_strap_pin(pinmux, gpio, 24,
                                           kTopDarjeelingMuxedPadsIoc2)
           << 4;
  return strap;
}

void pinmux_testutils_configure_pads(const dif_pinmux_t *pinmux,
                                     const pinmux_pad_attributes_t *attrs,
                                     size_t num_attrs) {
  for (size_t i = 0; i < num_attrs; ++i) {
    dif_pinmux_pad_attr_t desired_attr, actual_attr;
    CHECK_DIF_OK(dif_pinmux_pad_get_attrs(pinmux, attrs[i].pad, attrs[i].kind,
                                          &desired_attr));
    desired_attr.flags = attrs[i].flags;
    CHECK_DIF_OK(dif_pinmux_pad_write_attrs(pinmux, attrs[i].pad, attrs[i].kind,
                                            desired_attr, &actual_attr));
  }
}
