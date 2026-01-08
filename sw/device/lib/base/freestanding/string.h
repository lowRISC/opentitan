// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_FREESTANDING_STRING_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_FREESTANDING_STRING_H_

#include <stddef.h>

/**
 * @file
 * @brief C library string handling (Freestanding)
 *
 * This header implements the string.h standard header, as required by C24 S4p7,
 * and to the extent implemented by `sw/device/lib/base/memory.h`.
 *
 */

void *memcpy(void *dest, const void *src, size_t len);
void *memset(void *dest, int value, size_t len);
int memcmp(const void *lhs, const void *rhs, size_t len);
int memrcmp(const void *lhs, const void *rhs, size_t len);
void *memchr(const void *ptr, int value, size_t len);
void *memrchr(const void *ptr, int value, size_t len);

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_FREESTANDING_STRING_H_
