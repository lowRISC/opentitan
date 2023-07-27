// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_FREESTANDING_ISO646_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_FREESTANDING_ISO646_H_

/**
 * @file
 * @brief C library Alternative Spellings (Freestanding)
 *
 * This header implements the iso646.h standard header, as required by C11 S4p6.
 * See S7.9 of the same for a description.
 *
 * This file is provided only for standards compliance reason; including this
 * file is a style violation.
 */

// The below macro definitions cause clang-format to freak out somewhat, so we
// need to turn it off.
// clang-format off

#define and &&
#define and_eq &=
#define bitand &

#define or ||
#define or_eq |=
#define bitor |

#define xor ^
#define xor_eq ^=

#define not !
#define not_eq !=

#define compl ~

// clang-format on

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_FREESTANDING_ISO646_H_
