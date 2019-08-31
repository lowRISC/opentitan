// Generated register defines for gpio

// Copyright information found in source file:
// Copyright lowRISC contributors.

// Licensing information found in source file:
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _GPIO_REG_DEFS_
#define _GPIO_REG_DEFS_

// Interrupt State Register
#define GPIO_INTR_STATE(id) (GPIO##id##_BASE_ADDR + 0x0)

// Interrupt Enable Register
#define GPIO_INTR_ENABLE(id) (GPIO##id##_BASE_ADDR + 0x4)

// Interrupt Test Register
#define GPIO_INTR_TEST(id) (GPIO##id##_BASE_ADDR + 0x8)

// GPIO Input data read value
#define GPIO_DATA_IN(id) (GPIO##id##_BASE_ADDR + 0xc)

// GPIO direct output data write value
#define GPIO_DIRECT_OUT(id) (GPIO##id##_BASE_ADDR + 0x10)

// GPIO write data lower with mask.
#define GPIO_MASKED_OUT_LOWER(id) (GPIO##id##_BASE_ADDR + 0x14)
#define GPIO_MASKED_OUT_LOWER_DATA_MASK 0xffff
#define GPIO_MASKED_OUT_LOWER_DATA_OFFSET 0
#define GPIO_MASKED_OUT_LOWER_MASK_MASK 0xffff
#define GPIO_MASKED_OUT_LOWER_MASK_OFFSET 16

// GPIO write data upper with mask.
#define GPIO_MASKED_OUT_UPPER(id) (GPIO##id##_BASE_ADDR + 0x18)
#define GPIO_MASKED_OUT_UPPER_DATA_MASK 0xffff
#define GPIO_MASKED_OUT_UPPER_DATA_OFFSET 0
#define GPIO_MASKED_OUT_UPPER_MASK_MASK 0xffff
#define GPIO_MASKED_OUT_UPPER_MASK_OFFSET 16

// GPIO Output Enable.
#define GPIO_DIRECT_OE(id) (GPIO##id##_BASE_ADDR + 0x1c)

// GPIO write Output Enable lower with mask.
#define GPIO_MASKED_OE_LOWER(id) (GPIO##id##_BASE_ADDR + 0x20)
#define GPIO_MASKED_OE_LOWER_DATA_MASK 0xffff
#define GPIO_MASKED_OE_LOWER_DATA_OFFSET 0
#define GPIO_MASKED_OE_LOWER_MASK_MASK 0xffff
#define GPIO_MASKED_OE_LOWER_MASK_OFFSET 16

// GPIO write Output Enable upper with mask.
#define GPIO_MASKED_OE_UPPER(id) (GPIO##id##_BASE_ADDR + 0x24)
#define GPIO_MASKED_OE_UPPER_DATA_MASK 0xffff
#define GPIO_MASKED_OE_UPPER_DATA_OFFSET 0
#define GPIO_MASKED_OE_UPPER_MASK_MASK 0xffff
#define GPIO_MASKED_OE_UPPER_MASK_OFFSET 16

// GPIO interrupt enable for GPIO, rising edge.
#define GPIO_INTR_CTRL_EN_RISING(id) (GPIO##id##_BASE_ADDR + 0x28)

// GPIO interrupt enable for GPIO, falling edge.
#define GPIO_INTR_CTRL_EN_FALLING(id) (GPIO##id##_BASE_ADDR + 0x2c)

// GPIO interrupt enable for GPIO, level high.
#define GPIO_INTR_CTRL_EN_LVLHIGH(id) (GPIO##id##_BASE_ADDR + 0x30)

// GPIO interrupt enable for GPIO, level low.
#define GPIO_INTR_CTRL_EN_LVLLOW(id) (GPIO##id##_BASE_ADDR + 0x34)

// filter enable for GPIO input bits.
#define GPIO_CTRL_EN_INPUT_FILTER(id) (GPIO##id##_BASE_ADDR + 0x38)

#endif  // _GPIO_REG_DEFS_
// End generated register defines for gpio
