// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_LOG_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_LOG_H_

#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Prints a status message to UART0, formatted according to the format
 * string `format`.
 *
 * This function only supports the format specifiers required by the
 * mask ROM:
 * - %s, which prints a null-terminated string.
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
rom_error_t log_printf(const char *format, ...)
    __attribute__((format(printf, 1, 2)));

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_LOG_H_
