// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/gpio.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/common.h"
#include "sw/device/lib/runtime/hart.h"

void gpio_init(uint32_t oe) { REG32(GPIO_DIRECT_OE(0)) = oe; }

void gpio_write_bit(unsigned int bit, unsigned int val) {
  uint32_t mask = 0;
  uint32_t reg_val = 0;
  volatile uint32_t *gpio_masked_out_reg = 0;

  if (bit < 16) {
    gpio_masked_out_reg = (uint32_t *)GPIO_MASKED_OUT_LOWER(0);
  } else if (bit < 32) {
    gpio_masked_out_reg = (uint32_t *)GPIO_MASKED_OUT_UPPER(0);
  } else {
    /* bit must be less then 32 */
    abort();
  }
  bit %= 16;

  mask = (1 << bit);
  reg_val = (mask << 16) | ((val & 0x01) << bit);
  *gpio_masked_out_reg = reg_val;
}

void gpio_write_all(uint32_t val) { REG32(GPIO_DIRECT_OUT(0)) = val; }

uint32_t gpio_read(void) { return REG32(GPIO_DATA_IN(0)); }
