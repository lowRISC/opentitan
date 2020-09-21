// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_RUNTIME_PRINT_H_
#define OPENTITAN_SW_DEVICE_LIB_RUNTIME_PRINT_H_

#include <stdarg.h>
#include <stddef.h>

#include "sw/device/lib/dif/dif_uart.h"

/**
 * @file
 * @brief Libc-like printing facilities.
 *
 * This header provides libc-like printing facilities, which is agnostic of the
 * underlying hardware printing mechanism.
 *
 * We avoid using libc names here, since we do not support the full suite of
 * format specifier syntax, and use a different character sink type instead of
 * the traditional `FILE *`.
 *
 * All functions in this file should be machine word size agnostic, that is, the
 * same code should work correctly on both 32-bit and 64-bit machines, though
 * formatting, where the exact format style is unspecified, is allowed to vary
 * slightly on machine word size.
 */

/**
 * A buffer_sink_t represents a place to write bytes to, implemented as a
 * C-style "closure".
 *
 * It consists of a generic data pointer, which can hold instance-specific
 * information, and a sink function, which takes the data pointer, a buffer, and
 * that buffer's length.
 *
 * The sink function should return the number of bytes actually written.
 */
typedef struct buffer_sink {
  void *data;
  size_t (*sink)(void *data, const char *buf, size_t len);
} buffer_sink_t;

/**
 * Prints out a message to stdout, formatted according to the format string
 * `format`.
 *
 * The definition of "stdout" is not provided by this library; rather, it must
 * be initialized using `base_set_stdout()`.
 *
 * This function supports a subset of the format specifiers provided by standard
 * C `printf`. Those are, namely:
 * - %%, which prints a percent sign.
 * - %c, which prints the lowest byte of a uint32_t as a character.
 * - %s, which prints a NUL-terminated string.
 * - %d and %i, which print a signed decimal uint32_t.
 * - %u, which prints an unsigned decimal uint32_t.
 * - %o, which prints an unsigned octal uint32_t.
 * - %x and %X, which print an unsigned hex uint32_t.
 * - %p, which prints a pointer in a consistent but unspecified way.
 *
 * Additionally, three SystemVerilog format specifiers are supported:
 * - %h and %H, which are aliases for %x and %X, respectively.
 * - %b, which prints an unsigned binary uint32_t.
 *
 * Finally, an additional nonstandard format specifier is supported:
 * - %z, which takes a size_t followed by a pointer to a buffer, and prints
 *   out that many characters from the buffer.
 *
 * When compiled for a DV testbench, this function will not read any pointers,
 * and as such the specifiers %s and %z will behave as if they were printing
 * garbage, and are, as such, unsupported.
 *
 * This function furthermore supports width modifiers for integer specifiers,
 * such as `%10d`. It does not support dynamic widths like `%*d`, and will also
 * always pad with zeroes, rather than spaces.
 *
 * Of course, providing arguments for formatting which are incompatible with a
 * given format specifier is Undefined Behavior.
 *
 * Note that for logging in DV, the following script updates the format
 * specifiers supported in C above and changes them to match the SystemVerilog
 * language semantics: util/device_sw_utils/extract_sw_logs.py
 * It also makes fixes as needed for custom speficiers such as %z.
 *
 * @param format the format spec.
 * @param ... values to interpolate in the format spec.
 */
size_t base_printf(const char *format, ...);

/**
 * Prints out a message to stdout, formatted according to the format string
 * `format`.
 *
 * This function is identical to `base_printf`, except in that it takes a
 * `va_list` instead of having a vararg parameter. This function plays a role
 * analogous to `base_vfprintf`, for functions that wish to use the currently
 * set `stdout`.
 *
 * This function *does not* take ownership of `args`; callers are responsible
 * for calling `va_end`.
 *
 * See `base_printf()` for the semantics of the format specification.
 *
 * @param format the format spec.
 * @param args values to interpolate in the format spec.
 */
size_t base_vprintf(const char *format, va_list args);

/*
 * Prints a message to the buffer `buf`, capped at a given length.
 *
 * It goes without saying that the caller must ensure the given buffer is large
 * enough; failure to do so is Undefined Behavior.
 *
 * See `base_printf()` for the semantics of the format specification.
 *
 * @param buf a buffer to print to.
 * @param format the format spec.
 * @param ... values to interpolate in the format spec.
 */
size_t base_snprintf(char *buf, size_t len, const char *format, ...);

/**
 * Prints a message to the sink `out`.
 *
 * If `out.sink` is `NULL`, writes are treated as-if they were written to a
 * UNIX-like /dev/null: writes succeed, but the actual bytes are not printed
 * anywhere.
 *
 * See `base_printf()` for the semantics of the format specification.
 *
 * @param out a sink to print to.
 * @param format the format spec.
 * @param ... values to interpolate in the format spec.
 */
size_t base_fprintf(buffer_sink_t out, const char *format, ...);

/**
 * Prints a message to the sink `out`.
 *
 * This function is identical to `base_fprintf`, except in that it takes a
 * `va_list` instead of having a vararg parameter. This function is provided
 * not for calling directly, but rather for being called by functions that
 * already take a variable number of arguments, and wish to make use of
 * formatting facilities.
 *
 * This function *does not* take ownership of `args`; callers are responsible
 * for calling `va_end`.
 *
 * If `out.sink` is `NULL`, writes are treated as-if they were written to a
 * UNIX-like /dev/null: writes succeed, but the actual bytes are not printed
 * anywhere.
 *
 * See `base_printf()` for the semantics of the format specification.
 *
 * @param out a sink to print to.
 * @param format the format spec.
 * @param args values to interpolate in the format spec.
 */
size_t base_vfprintf(buffer_sink_t out, const char *format, va_list args);

/**
 * Sets what the "stdout" sink is, which is used by `base_printf()`.
 *
 * The default sink behaves like /dev/null on a standard UNIX system: writes
 * are treated as successful, but the contents of buffers are ignored.
 *
 * As such, this function must be called for printed messages to wind up
 * somewhere.
 *
 * Passing in `NULL` instead of a real function pointer will reset stdout to
 * the default /dev/null behavior.
 *
 * @param out the sink to use for "default" printing.
 */
void base_set_stdout(buffer_sink_t out);

/**
 * Configures UART stdout for `base_print.h` to use.
 *
 * Note that this function will save `uart` in a global variable, so the pointer
 * must have static storage duration.
 *
 * @param uart The UART handle to use for stdout.
 */
void base_uart_stdout(const dif_uart_t *uart);

#endif  // OPENTITAN_SW_DEVICE_LIB_RUNTIME_PRINT_H_
