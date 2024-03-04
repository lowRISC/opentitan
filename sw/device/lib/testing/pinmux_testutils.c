// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/pinmux_testutils.h"

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/devicetables/dt.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/testing/test_framework/check.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

void pinmux_testutils_init(dif_pinmux_t *pinmux) {
  uint32_t cfg_len = dt_pinctrl_boot_periphmux_config_len();
  for (uint32_t idx = 0; idx < cfg_len; idx++) {
    dt_pinctrl_cfg_t cfg = dt_pinctrl_get_boot_periphmux_config(idx);
    dif_pinmux_index_t mux_id = dt_pinctrl_mux_from_cfg(cfg);
    dif_pinmux_index_t sel_id = dt_pinctrl_selection_from_cfg(cfg);
    CHECK_DIF_OK(dif_pinmux_input_select(pinmux, mux_id, sel_id));
  }
  cfg_len = dt_pinctrl_boot_padmux_config_len();
  for (uint32_t idx = 0; idx < cfg_len; idx++) {
    dt_pinctrl_cfg_t cfg = dt_pinctrl_get_boot_padmux_config(idx);
    dif_pinmux_index_t mux_id = dt_pinctrl_mux_from_cfg(cfg);
    dif_pinmux_index_t sel_id = dt_pinctrl_selection_from_cfg(cfg);
    CHECK_DIF_OK(dif_pinmux_output_select(pinmux, mux_id, sel_id));
  }

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
        dif_pinmux_pad_write_attrs(pinmux, kTopEarlgreyDirectPadsUsbdevUsbDp,
                                   kDifPinmuxPadKindDio, in_attr, &out_attr));
    CHECK_DIF_OK(
        dif_pinmux_pad_write_attrs(pinmux, kTopEarlgreyDirectPadsUsbdevUsbDn,
                                   kDifPinmuxPadKindDio, in_attr, &out_attr));
  }
#endif
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
    // Only IOR6, IOR7, and IOR10 to IOR13 are available for use as GPIOs.
    return 0xfc000000;
  } else {
    return 0xffffffff;
  }
}

uint32_t pinmux_testutils_read_strap_pin(dif_pinmux_t *pinmux, dif_gpio_t *gpio,
                                         dif_gpio_pin_t io,
                                         top_earlgrey_muxed_pads_t pad) {
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
                                           kTopEarlgreyMuxedPadsIoc0);
  strap |= pinmux_testutils_read_strap_pin(pinmux, gpio, 23,
                                           kTopEarlgreyMuxedPadsIoc1)
           << 2;
  strap |= pinmux_testutils_read_strap_pin(pinmux, gpio, 24,
                                           kTopEarlgreyMuxedPadsIoc2)
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
