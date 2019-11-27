// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _GPIO_H_
#define _GPIO_H_

#include <stdint.h>

#include "gpio_regs.h"  // Generated.

#define GPIO0_BASE_ADDR 0x40010000

#define GPIO_REG_DEF(id, rname) (REG_DEF(GPIO, id, rname))
#define GPIO_DIRECT_OE(id) (GPIO_REG_DEF(id, DIRECT_OE))
#define GPIO_MASKED_OUT_LOWER(id) (GPIO_REG_DEF(id, MASKED_OUT_LOWER))
#define GPIO_MASKED_OUT_UPPER(id) (GPIO_REG_DEF(id, MASKED_OUT_UPPER))
#define GPIO_DIRECT_OUT(id) (GPIO_REG_DEF(id, DIRECT_OUT))
#define GPIO_DATA_IN(id) (GPIO_REG_DEF(id, DATA_IN))

#define GPIO_BOOTSTRAP_BIT_MASK 0x20000

/**
 * @param oe bits to use as output
 */
void gpio_init(uint32_t oe);

void gpio_write_bit(unsigned int bit, unsigned int val);
void gpio_write_all(uint32_t val);
uint32_t gpio_read(void);

#endif
