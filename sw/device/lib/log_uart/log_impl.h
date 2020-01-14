// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_LOG_UART_LOG_IMPL_H_
#define OPENTITAN_SW_DEVICE_LIB_LOG_UART_LOG_IMPL_H_

#include "sw/device/lib/print_log.h"
#include "sw/device/lib/uart.h"

// Stringify stuff.
#define _LOG_IMPL_STRINGIFY(a) _LOG_IMPL_STRINGIFY_INNER(a)
#define _LOG_IMPL_STRINGIFY_INNER(a) #a

/**
 * Log type and verbosity string constants
 */
#define LOG_TYPE_INFO "INFO"
#define LOG_TYPE_WARNING "WARNING"
#define LOG_TYPE_ERROR "ERROR"
#define LOG_TYPE_FATAL "FATAL"

/**
 * Log header helper macro
 *
 * This macro constructs the log header in the following way:
 * If LOG_HEADER_INCL_FILE_LINE flag is set:      TYPE (file:line):
 * If LOG_HEADER_INCL_FILE_LINE flag is not set:  TYPE:
 *
 * Log verbosity is currently unused, since the volume of messages
 * is not expected to be very high.
 */
#ifdef LOG_HEADER_INCL_FILE_LINE
#define LOG_HEADER(log_type, verbosity) \
  "" log_type "" verbosity              \
  ""                                    \
  " (" __FILE__ ":" _LOG_IMPL_STRINGIFY(__LINE__) "): "
#else
#define LOG_HEADER(log_type, verbosity) \
  "" log_type "" verbosity              \
  ""                                    \
  ": "
#endif

/**
 * Print log helper macro
 *
 * This macro calls the log_print() function to process format string and its
 * type specifier arguments. It passes uart_send_char to print the message
 * string character by character via UART. Do not invoke this macro directly;
 * use the logging APIs in log.h (which serve as the generic APIs and invoke
 * this macro underneath) instead.
 */
#define PRINT_LOG(log_header, ...) \
  print_log(&uart_send_char, log_header __VA_ARGS__);

#endif  // OPENTITAN_SW_DEVICE_LIB_LOG_UART_LOG_IMPL_H_
