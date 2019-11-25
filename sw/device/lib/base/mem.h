// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef SW_DEVICE_LIB_BASE_MEM_H_
#define SW_DEVICE_LIB_BASE_MEM_H_

#include "sw/device/lib/base/types.h"

/**
 * Standard memory operations modeled after those specified in <string.h>,
 * with some extra convenience definitions.
 */

#define VOLATILE_8(address) *((volatile uint8 *)(address))
#define VOLATILE_16(address) *((volatile uint16 *)(address))
#define VOLATILE_32(address) *((volatile uint32 *)(address))

#define GET_BIT(val, bit) ((val) & (1 << (bit)))
#define SET_BIT(val, bit) ((val) |= 1 << (bit))
#define CLR_BIT(val, bit) ((val) &= ~(1 << (bit)))

void *base_memcpy(void *restrict dest, const void *restrict src, usize count);

void *base_memset(void *dest, int ch, usize count);

usize base_strlen(const char *str);

#endif  // SW_DEVICE_LIB_BASE_TYPES_H_