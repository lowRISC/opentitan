// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DBG_PRINT_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DBG_PRINT_H_

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * An intentionally pared-down implementation of `printf()` that writes
 * to UART0.
 *
 * This function only supports the format specifiers required by the
 * ROM:
 * - %c, which prints a single character.
 * - %d, which prints a signed int in decimal.
 * - %u, which prints an unsigned int in decimal.
 * - %s, which prints a nul-terminated string.
 * - %p, which prints pointer in hexadecimal.
 * - %x, which prints an `unsigned int` in hexadecimal using lowercase
 *   characters.
 *
 * No modifiers are supported and the leading zeros in hexidecimal
 * values are always printed.
 *
 * Note: unfortunately `uint32_t` is not necessarily an alias for
 * `unsigned int`. An explicit cast is therefore necessary when printing
 * `uint32_t` values using the `%x` format specifier in order to satisfy
 * the `printf` format checker (`-Wformat`).
 *
 * @param format The format specifier.
 * @param ... The values to interpolate in the format.
 * @return The result of the operation.
 */
void dbg_printf(const char *format, ...) __attribute__((format(printf, 1, 2)));

/**
 * Print the ePMP configuration to the console.
 */
void dbg_print_epmp(void);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DBG_PRINT_H_
