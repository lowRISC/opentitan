// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/rv_timer.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "sw/device/lib/base/log.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/irq.h"
#include "sw/device/lib/pinmux.h"
#include "sw/device/lib/testing/test_main.h"

static dif_gpio_t gpio;
// Flag to indicate that the interrupt was seen. Declared as volatile since it
// is referenced in the ISR routine as well as in the main program flow.
static volatile bool intr_handling_success;
static const uint32_t hart = (uint32_t)kTopEarlgreyPlicTargetIbex0;

bool test_main(void) {
  const uint64_t cmp = 0x000000000000000F;

  pinmux_init();
  // Enable GPIO: 0-7 and 16 is input, 8-15 is output
  dif_gpio_config_t gpio_config = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR)};
  dif_gpio_init(&gpio_config, &gpio);
  dif_gpio_output_mode_all_set(&gpio, 0xFF00);

  irq_global_ctrl(true);
  irq_timer_ctrl(true);
  rv_timer_intr_enable(hart, true);

  intr_handling_success = false;
  rv_timer_set_us_tick(hart);
  rv_timer_set_cmp(hart, cmp);
  rv_timer_ctrl(hart, true);

  dif_gpio_all_write(&gpio, 0xFF00);  // all LEDs on

  while (1) {
    if (intr_handling_success) {
      break;
    }
  }

  dif_gpio_all_write(&gpio, 0xAA00);  // Test Completed

  return true;
}

// Override weak default function
void handler_irq_timer(void) {
  LOG_INFO("In Interrupt handler!");
  rv_timer_ctrl(hart, false);
  rv_timer_clr_all_intrs();
  intr_handling_success = true;
}
