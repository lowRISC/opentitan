// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/gpio.h"

#include "sw/device/silicon_creator/lib/base/abs_mmio.h"

#include "gpio_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

enum {
  kBase = TOP_EARLGREY_GPIO_BASE_ADDR,
};

uint32_t gpio_read(void) {
  return abs_mmio_read32(kBase + GPIO_DATA_IN_REG_OFFSET);
}
