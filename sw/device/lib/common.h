// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_COMMON_H_
#define OPENTITAN_SW_DEVICE_LIB_COMMON_H_

#define REG8(add) *((volatile uint8_t *)(add))
#define REG16(add) *((volatile uint16_t *)(add))
#define REG32(add) *((volatile uint32_t *)(add))
#define SETBIT(val, bit) (val | 1 << bit)
#define CLRBIT(val, bit) (val & ~(1 << bit))

#define ARRAYSIZE(x) (sizeof(x) / sizeof(x[0]))

#endif  // OPENTITAN_SW_DEVICE_LIB_COMMON_H_
