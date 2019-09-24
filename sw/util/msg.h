// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _MSG_H_
#define _MSG_H_

#include "common.h"
#include "msg_print.h"

/** Generic msg print function that takes variable # of args to print msgs via
 * real hardware
 *
 * Function uses a formatted string as input with variable number of args.
 * This function is used for real SW builds (not DV). To ensure portability of
 * code across different platforms (DV simulations as well as FPGA based
 * emulations with real SW), this method should NOT be called directly. Instead,
 * please use predefined macros below instead.
 * This function takes a function pointer as an arg to preform a single char
 * write using the real HW. That has to be defined in the flow specific header
 * file msg_<flow>/msg_print.h. See msg_uart/msg_print.h for example.
 *
 * DO NOT CALL THIS FUNCTION DIRECTLY! Use the macro flavors defined in msg.h.
 *
 * @param output: function pointer that takes single char input and 'prints' it
 * via real HW such as UART.
 * @param msg_header: title or header for a msg. If the standard msg print macro
 * flavors are used (defined below), then msg_header resolves to a string
 * indicating msg type, verbosity, file and line (what that looks like is
 * defined using the MSG_HEADER macro (see details below).
 * @param fmt: actual formatted msg string (printf style)
 * @param ...: variable # of args passed to the formatted msg (NOTE: use of only
 * integer-like type specifiers recommended)
 */
void msg_print(void (*output)(char), const char *msg_header, const char *fmt,
               ...);

/** Standard msg print macro flavors
 *
 * The following flavor of macros prepend the actual print msg with a standard
 * header.
 * The header contains the following info:
 *  msg_type:     info, warning, error or fatal
 *  verbosity:    (applicable only to info) none, low, medium, high, full
 *                and debug. These conform to the UVM DV standard. We will
 *                however mostly print info msgs with low verbosity.
 *  file name:    name of the file using __FILE__
 *  line number:  line where the print originated using __LINE__
 *
 * How this header is constructed is target / impl specific using the following
 * macros that are to be defined in the <target>/msg_print.h.
 *
 * MSG_HEADER(a, b): takes msg type and verbosity based on following
 * flavors as args and adds __FILE__ and __LINE__ info.
 *
 * MSG_TYPE_*: these indicate the msg type as a const string
 *
 * MSG_VERB_*: these indicate the verbosity as const string
 *
 * MSG_PRINT(msg_header, fmt, ...): This calls the msg_print() function
 * underneath with the appropriate 'output' arg.
 * See existing <target>/msg_print.h for example.
 */
#define MSG_INFO(fmt, ...) \
  MSG_PRINT(MSG_HEADER(MSG_TYPE_INFO, MSG_VERB_NONE), fmt, __VA_ARGS__)

#define MSG_INFO_LOW(fmt, ...) \
  MSG_PRINT(MSG_HEADER(MSG_TYPE_INFO, MSG_VERB_LOW), fmt, __VA_ARGS__)

#define MSG_INFO_MEDIUM(fmt, ...) \
  MSG_PRINT(MSG_HEADER(MSG_TYPE_INFO, MSG_VERB_MEDIUM), fmt, __VA_ARGS__)

#define MSG_INFO_HIGH(fmt, ...) \
  MSG_PRINT(MSG_HEADER(MSG_TYPE_INFO, MSG_VERB_HIGH), fmt, __VA_ARGS__)

#define MSG_INFO_FULL(fmt, ...) \
  MSG_PRINT(MSG_HEADER(MSG_TYPE_INFO, MSG_VERB_FULL), fmt, __VA_ARGS__)

#define MSG_INFO_DEBUG(fmt, ...) \
  MSG_PRINT(MSG_HEADER(MSG_TYPE_INFO, MSG_VERB_DEBUG), fmt, __VA_ARGS__)

#define MSG_WARNING(fmt, ...) \
  MSG_PRINT(MSG_HEADER(MSG_TYPE_WARNING, ""), fmt, __VA_ARGS__)

#define MSG_ERROR(fmt, ...) \
  MSG_PRINT(MSG_HEADER(MSG_TYPE_ERROR, ""), fmt, __VA_ARGS__)

#define MSG_FATAL(fmt, ...) \
  MSG_PRINT(MSG_HEADER(MSG_TYPE_FATAL, ""), fmt, __VA_ARGS__)

#endif  // _MSG_H_
