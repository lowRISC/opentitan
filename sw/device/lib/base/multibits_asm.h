// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_MULTIBITS_ASM_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_MULTIBITS_ASM_H_

/**
 * Multi-bit boolean values for use in assembly code.
 *
 * Please use `multibits.h` instead when writing C code.
 */

/**
 * 4-bits boolean values
 */
#define MULTIBIT_ASM_BOOL4_TRUE 0xA
#define MULTIBIT_ASM_BOOL4_FALSE 0x5

/**
 * 8-bits boolean values
 */
#define MULTIBIT_ASM_BOOL8_TRUE 0x5A
#define MULTIBIT_ASM_BOOL8_FALSE 0xA5

/**
 * 12-bits boolean values
 */
#define MULTIBIT_ASM_BOOL12_TRUE 0xA5A
#define MULTIBIT_ASM_BOOL12_FALSE 0x5A5

/**
 * 16-bits boolean values
 */
#define MULTIBIT_ASM_BOOL16_TRUE 0x5A5A
#define MULTIBIT_ASM_BOOL16_FALSE 0xA5A5

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_MULTIBITS_ASM_H_
