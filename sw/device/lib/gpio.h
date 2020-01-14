// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_GPIO_H_
#define OPENTITAN_SW_DEVICE_LIB_GPIO_H_

#include <stdint.h>

#include "gpio_regs.h"  // Generated.

#define GPIO0_BASE_ADDR 0x40010000

#define GPIO_BOOTSTRAP_BIT_MASK 0x20000

/**
 * @param oe bits to use as output
 */
void gpio_init(uint32_t oe);

void gpio_write_bit(unsigned int bit, unsigned int val);
void gpio_write_all(uint32_t val);
uint32_t gpio_read(void);

#endif  // OPENTITAN_SW_DEVICE_LIB_GPIO_H_
