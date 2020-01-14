// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_LOG_H_
#define OPENTITAN_SW_DEVICE_LIB_LOG_H_

#ifdef DV_SIM
#include "sw/device/lib/log_uart/log_impl.h"
#else
#include "sw/device/lib/log_uart/log_impl.h"
#endif

/**
 * Generic logging APIs
 *
 * The logging APIs below take a format string with a variable number of
 * arguments for the type specifiers. The APIs are designed to provide a way
 * for attaching the message type, verbosity, file name and the line number
 * information along with the message to provide an easier path to debug.
 * These parameters form the message header which is prepended to the actual
 * message being printed. The following is a brief description of these:
 *
 *  log_type:     Severity of the message:
 *                info, warning, error or fatal
 *                This is indicated using LOG_TYPE_* set of macros which are
 *                set to empty strings by default.
 *
 *  verbosity:    Verbosity of the message (applicable only to info messages):
 *                none, low, medium, high, full and debug.
 *                Based on the desired verbosity, the visibility of certain
 *                messages can be turned off. This is expected to be done
 *                externally (for example, if the messages go to a log,
 *                the desired verbosity messages can be searched and filtered
 *                out). This is indicated using the LOG_VERB_* set of macros
 *                which are set to empty strings by default.
 *
 *  file name:    Name of the file using __FILE__
 *
 *  line number:  Line where the print originated using __LINE__
 *
 * The construction of the log header using the above parameters is provided
 * by the LOG_HEADER() helper macro.
 *
 * Once the header is constructed, another API is invoked that takes the header
 * and the original message as arguments and prints the whole message using the
 * desired implementation. This is provided by the PRINT_LOG() helper macro.
 *
 * All of these macros defined in this file can be overridden to customize the
 * flow based on the desired outcome. This is done in the log_impl.h header
 * file, placed in the sw/util/log_<impl> directory. The correct log_impl.h is
 * selected by the build system which resolves the dependency based on the
 * desired implementation.
 *
 * Supported format type specifiers
 * The list of supported format specifiers is limited to integer / numerical
 * types to maintain compatibility of the source code across different targets
 * such as DV, Verilator and FPGA based simulations. These are as follows:
 * %b:  Print binary [SystemVerilog style].
 * %i:  Signed decimal.
 * %d:  Signed decimal.
 * %u:  Unsigned decimal.
 * %o:  Octal.
 * %c:  Single character byte.
 * %X:  Upper case hex.
 * %H:  Upper case hex [SystemVerilog style].
 * %x:  Lower case hex.
 * %h:  Lower case hex [SystemVerilog style].
 * %%:  Escape '%'.
 *
 * In addition, there is an elementary support for specifing the width (as a
 * positive number) to set the minimun number of digits to be print:
 * %3d: Print minimum 3 digits, if fewer than 3 is available, then pad with 0s.
 */

/**
 * Log type and verbosity string constants
 *
 * These are strings used by the LOG_HEADER helper macro to construct the
 * header. These are set to empty strings - override these with the desired
 * strings in the implementation-specific log_impl.h header.
 */
#ifndef LOG_TYPE_INFO
#define LOG_TYPE_INFO ""
#endif

#ifndef LOG_TYPE_WARNING
#define LOG_TYPE_WARNING ""
#endif

#ifndef LOG_TYPE_ERROR
#define LOG_TYPE_ERROR ""
#endif

#ifndef LOG_TYPE_FATAL
#define LOG_TYPE_FATAL ""
#endif

#ifndef LOG_VERB_NONE
#define LOG_VERB_NONE ""
#endif

#ifndef LOG_VERB_LOW
#define LOG_VERB_LOW ""
#endif

#ifndef LOG_VERB_MEDIUM
#define LOG_VERB_MEDIUM ""
#endif

#ifndef LOG_VERB_HIGH
#define LOG_VERB_HIGH ""
#endif

#ifndef LOG_VERB_FULL
#define LOG_VERB_FULL ""
#endif

#ifndef LOG_VERB_DEBUG
#define LOG_VERB_DEBUG ""
#endif

/**
 * Log header helper macro
 *
 * This macro provides a way to construct the log header string using the above
 * string constants.  This is set to an empty string - override this with the
 * desired header construction in the implementation-specific log_impl.h
 * header.
 */
#ifndef LOG_HEADER
#define LOG_HEADER(log_type, verbosity) ""
#endif

/**
 * Print log helper macro
 *
 * The generic logging APIs below are expected to invoke this underneath
 * and provide a way to suppliment the message being printed with a header.
 * Override this in the implementation-specific log_impl.h header.
 */
#ifndef PRINT_LOG
#warning PRINT_LOG undefined: it will result in vacuous invocation
#define PRINT_LOG(log_header, ...)
#endif

/**
 * Logging APIs
 *
 * The following are a set of generic message APIs available for use in
 * OpenTitan SW. These invoke the PRINT_LOG() helper macro which is vacuously
 * defined above. The LOG_HEADER() helper macro is invoked in place of the
 * "log_header' argument to PRINT_LOG(). LOG_HEADER() is also vacuously defined
 * above. These helper macros can be overridden in the implementation-specific
 * log_impl.h macro to achieve the desired outcome.
 * The generic message APIs themselves can also be overridden if there is a
 * desire to do so.
 *
 * @param fmt:    Format string message with type specifiers. To maintain
 *                compatibility with the message API implementation for DV, the
 *                type specifiers are limited to integer types.
 * @param ...:    Arguments passed to the format string based on the type
 *                specifiers in fmt.
 */
// Print an info message with no verbosity.
#ifndef LOG_INFO
#define LOG_INFO(...) \
  PRINT_LOG(LOG_HEADER(LOG_TYPE_INFO, LOG_VERB_NONE), __VA_ARGS__)
#endif

// Print an info message with low verbosity.
#ifndef LOG_INFO_LOW
#define LOG_INFO_LOW(...) \
  PRINT_LOG(LOG_HEADER(LOG_TYPE_INFO, LOG_VERB_LOW), __VA_ARGS__)
#endif

// Print an info message with medium verbosity.
#ifndef LOG_INFO_MEDIUM
#define LOG_INFO_MEDIUM(...) \
  PRINT_LOG(LOG_HEADER(LOG_TYPE_INFO, LOG_VERB_MEDIUM), __VA_ARGS__)
#endif

// Print an info message with high verbosity.
#ifndef LOG_INFO_HIGH
#define LOG_INFO_HIGH(...) \
  PRINT_LOG(LOG_HEADER(LOG_TYPE_INFO, LOG_VERB_HIGH), __VA_ARGS__)
#endif

// Print an info message with full verbosity.
#ifndef LOG_INFO_FULL
#define LOG_INFO_FULL(...) \
  PRINT_LOG(LOG_HEADER(LOG_TYPE_INFO, LOG_VERB_FULL), __VA_ARGS__)
#endif

// Print an info message with debug verbosity.
#ifndef LOG_INFO_DEBUG
#define LOG_INFO_DEBUG(...) \
  PRINT_LOG(LOG_HEADER(LOG_TYPE_INFO, LOG_VERB_DEBUG), __VA_ARGS__)
#endif

// Print a warning message.
#ifndef LOG_WARNING
#define LOG_WARNING(...) \
  PRINT_LOG(LOG_HEADER(LOG_TYPE_WARNING, ""), __VA_ARGS__)
#endif

// Print an error message.
#ifndef LOG_ERROR
#define LOG_ERROR(...) PRINT_LOG(LOG_HEADER(LOG_TYPE_ERROR, ""), __VA_ARGS__)
#endif

// Print a fatal error message.
#ifndef LOG_FATAL
#define LOG_FATAL(...) PRINT_LOG(LOG_HEADER(LOG_TYPE_FATAL, ""), __VA_ARGS__)
#endif

#endif  // OPENTITAN_SW_DEVICE_LIB_LOG_H_
