// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_FREESTANDING_STDALIGN_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_FREESTANDING_STDALIGN_H_

/**
 * @file
 * @brief C library Alignment (Freestanding)
 *
 * This header implements the stdalign.h standard header, as required by C11
 * S4p6. This header is specified in detail in S7.15 of the same.
 */

#define alignas _Alignas
#define __alignas_is_defined 1

#define alignof _Alignof
#define __alignof_is_defined 1

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_FREESTANDING_STDALIGN_H_
