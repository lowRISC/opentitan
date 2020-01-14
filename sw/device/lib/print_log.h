// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_PRINT_LOG_H_
#define OPENTITAN_SW_DEVICE_LIB_PRINT_LOG_H_

// Pointer to a function that prints a character.
typedef void (*print_char_func)(char);

/**
 * Generic print log function that prints a format string with variable
 * number of type specifiers and arguments through a real hardware in the chip
 *
 * Function uses a format string as input which can contain a variable number
 * of type specifiers. These are fulfilled with with variable number of
 * corresponding arguments. It also takes a function pointer (which itself
 * takes a single char argument as input) as an argument to print (write) the
 * whole message string char by char through the HW IOs.
 *
 * To ensure portability of code across different platforms (DV simulations,
 * FPGA based emulations with  production SW, simulations using Verilator,
 * etc.), DO NOT CALL THIS FUNCTION DIRECTLY! Instead please use the generic
 * logging APIs defined in msg.h.
 * Also, the list of supported format specifiers is limited to integer types
 * (%c, %d, %x, %X).
 *
 * @param print_char: Function pointer that takes single character as input and
 *                    writes it to a HW in the chip such as UART for printing.
 * @param fmt:    Format string message with type specifiers. To maintain
 *                compatibility with the logging API implementation for DV, the
 *                type specifiers are limited to integer types.
 * @param ...:    Arguments passed to the format string based on the type
 *                specifiers in fmt.
 */
void print_log(print_char_func print_char, const char *fmt, ...);

#endif  // OPENTITAN_SW_DEVICE_LIB_PRINT_LOG_H_
