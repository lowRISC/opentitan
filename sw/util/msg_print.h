// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _MSG_PRINT_H_
#define _MSG_PRINT_H_

#include "common.h"

/** Generic msg print function that takes variable # of args to print msgs via
 * real hardware
 *
 * Function uses a formatted string as input with variable number of args.
 * This function is used for real SW builds (not DV). This function takes a
 * function pointer (which itself takes a single char arg as input) as an arg to
 * print (write) the whole msg string char by char using the real HW IOs.
 *
 * To ensure portability of code across different platforms (DV simulations,
 * FPGA based emulations with  production SW, simulations using Verilator,
 * etc.), DO NOT CALL THIS FUNCTION DIRECTLY! Instead please use the generic msg
 * print APIs defined in msg_api.h.
 *
 * @param output:     function pointer that takes single char input and 'prints'
 *                    it via real HW such as UART.
 * @param fmt:        actual formatted msg string (printf style)
 * @param ...:        variable # of args passed to the formatted msg (NOTE: use
 *                    of only integer-like type specifiers are recommended)
 */
void msg_print(void (*output)(char), const char *fmt, ...);

#endif  // _MSG_PRINT_H_
