// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>

#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/manifest_def.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

static dif_gpio_t gpio;
static dif_pinmux_t pinmux;

static const dif_gpio_pin_t kGpioPinIoa5 = 0;

bool test_main(void) {
  // Initialize pinmux and GPIO peripherals.
  CHECK_DIF_OK(
      dif_gpio_init(mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR), &gpio));
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIoa5,
                                        kTopEarlgreyPinmuxOutselGpioGpio0));
  CHECK_DIF_OK(
      dif_gpio_output_set_enabled_all(&gpio, 0x1));  // Enable first GPIO.
  CHECK_DIF_OK(
      dif_gpio_write_all(&gpio, /*write_val=*/0));  // Intialize all to 0.

  // Toggle IOA5.
  CHECK_DIF_OK(dif_gpio_write(&gpio, kGpioPinIoa5, true));
  busy_spin_micros(100);
  CHECK_DIF_OK(dif_gpio_write(&gpio, kGpioPinIoa5, false));
  busy_spin_micros(100);
  CHECK_DIF_OK(dif_gpio_write(&gpio, kGpioPinIoa5, true));

  return true;
}
