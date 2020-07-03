// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_pinmux.h"


#include "sw/device/lib/base/log.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/runtime/check.h"
#include "sw/device/lib/testing/test_main.h"
#include "sw/device/lib/testing/test_status.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

static dif_pinmux_t pinmux;
static dif_gpio_t gpio;

static void difs_initialise(void) {
  dif_gpio_config_t gpio_config = {
    .base_addr = mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR),
  };

  dif_gpio_result_t gpio_result = dif_gpio_init(&gpio_config, &gpio);
  CHECK(gpio_result != kDifGpioOk, "Failed to initialise GPIO");

  mmio_region_t pinmux_base_addr =
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_BASE_ADDR);

  dif_pinmux_init_result_t pinmux_result =
    dif_pinmux_init(pinmux_base_addr, &pinmux);
  CHECK(pinmux_result != kDifPinmuxInitOk, "Failed to initialise Pinmux");
}

// 
/**
 * Creates a connection between GPIO0 output and GPIO1 input.
 *
 * Pinmux creates a connection between GPIO0 and Pad Control MIO0 outputs,
 * and GPIO1 and Pad Control MIO0 inputs. What it means in practice, is that
 * driven value on GPIO0 can be read on GPIO1, or to put it simply:
 * GPIO0 => MIO0 => GPIO1.
 *
 * Please see Pad Control documentation for more information:
 * https://docs.opentitan.org/hw/ip/padctrl/doc/index.html#design-details
 * In particular "pad wrapper", which explains the relationship between
 * Pad Control internal input/output signals and the external INOUT pins. 
 */
void gpio0_output_to_gpio1_input(void) {
  dif_pinmux_result_t result =
    dif_pinmux_outsel_set(&pinmux, 0, kDifPinmuxOutselFirstOut);
  CHECK(result != kDifPinmuxOk, "Failed to connect GPIO0 and MIO0 outputs");

  result = dif_pinmux_insel_set(&pinmux, 1, kDifPinmuxInselFirstIn);
  CHECK(result != kDifPinmuxOk, "Failed to connect GPIO1 and MIO0 inputs");
}

bool test_main(void) {
  difs_initialise();
  gpio0_output_to_gpio1_input();

  return true;
}
