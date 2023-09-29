// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/ip/pinmux/test/utils/pinmux_testutils.h"

#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/ip/base/dif/dif_base.h"
#include "sw/ip/gpio/dif/dif_gpio.h"
#include "sw/ip/pinmux/dif/dif_pinmux.h"
#include "sw/lib/sw/device/arch/device.h"
#include "sw/lib/sw/device/base/macros.h"
#include "sw/lib/sw/device/base/status.h"
#include "sw/lib/sw/device/runtime/hart.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"

void pinmux_testutils_init(dif_pinmux_t *pinmux) {}

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
                                         dif_pinmux_index_t pad) {
  // Turn off the pull enable on the pad and read the IO.
  dif_pinmux_pad_attr_t attr = {.flags = 0};
  dif_pinmux_pad_attr_t attr_out;
  CHECK_DIF_OK(dif_pinmux_pad_write_attrs(pinmux, pad, kDifPinmuxPadKindDio,
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
  CHECK_DIF_OK(dif_pinmux_pad_write_attrs(pinmux, pad, kDifPinmuxPadKindDio,
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
                                           kTopDarjeelingDirectPadsGpioGpio22);
  strap |= pinmux_testutils_read_strap_pin(pinmux, gpio, 23,
                                           kTopDarjeelingDirectPadsGpioGpio23)
           << 2;
  strap |= pinmux_testutils_read_strap_pin(pinmux, gpio, 24,
                                           kTopDarjeelingDirectPadsGpioGpio24)
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
