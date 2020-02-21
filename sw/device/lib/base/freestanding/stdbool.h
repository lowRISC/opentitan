// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_FREESTANDING_STDBOOL_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_FREESTANDING_STDBOOL_H_

/**
 * @file
 * @brief C Library Boolean type and values (Freestanding)
 *
 * This header implements the stdbool.h standard header, as required by C11
 * S4p6. This header is specified in detail in S7.18 of the same.
 */

#define bool _Bool
#define true 1
#define false 0

#define __bool_true_false_are_defined 1

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_FREESTANDING_STDBOOL_H_
