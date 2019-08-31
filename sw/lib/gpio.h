// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _GPIO_H_
#define _GPIO_H_

#include <stdint.h>

#include "gpio_regs.h"

#define GPIO0_BASE_ADDR 0x40010000

void gpio_init(uint32_t oe);
void gpio_write_bit(unsigned int bit, unsigned int val);
void gpio_write_all(uint32_t val);
uint32_t gpio_read(void);

#endif
