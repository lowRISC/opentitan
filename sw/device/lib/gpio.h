// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _GPIO_H_
#define _GPIO_H_

#include "sw/device/lib/base/types.h"

#include "gpio_regs.h"  // Generated.

#define GPIO0_BASE_ADDR 0x40010000

#define GPIO_BOOTSTRAP_BIT_MASK 0x20000

/**
 * @param oe bits to use as output
 */
void gpio_init(uint32 oe);

void gpio_write_bit(unsigned int bit, unsigned int val);
void gpio_write_all(uint32 val);
uint32 gpio_read(void);

#endif
