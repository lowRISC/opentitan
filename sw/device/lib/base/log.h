// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_LOG_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_LOG_H_

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"

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
 * Log macros support formatting specifiers; see print.h for details the subset
 * of C specifier syntax supported.
 *
 * The precise mechanism for logging is dependent on the target device. On core
 * devices, like Verilator, logs are printed using whatever `stdout` is set to
 * in print.h. DV testbenches may use an alternative, more efficient mechanism.
 * In DV mode, some format specifiers may be unsupported, such as %s.
 */

/**
 * Log severities available.
 *
 * Additional log severities can be added as necessary.
 */
typedef enum log_severity {
  kLogSeverityInfo,
  kLogSeverityWarn,
  kLogSeverityError,
  kLogSeverityFatal,
} log_severity_t;

/**
 * Provides additional information (metadata) pertaining to the log to aid
 * debug.
 *
 * Any modification to this struct must be made with caution due to external
 * assumptions. A post-processing script parses the ELF file and extracts the
 * log fields. The said script uses 20-byte size as the delimiter to collect the
 * log fields. Any changes to this struct must be accompanied with the updates
 * to the script, located here:
 * util/device_sw_utils/extract_sw_logs.py.
 */
typedef struct log_fields {
  /**
   * Indicates the severity of the log.
   */
  log_severity_t severity;
  /**
   * Pointer to the file name that is invoking the LOG_* methods.
   */
  const char *file_name;
  /**
   * Indicates the line number of the log.
   */
  uint32_t line;
  /**
   * Indicates the number of arguments passed to the format string. This is
   * used only in the SW logging method for DV.
   */
  uint32_t nargs;
  /**
   * Indicates the format string.
   */
  const char *format;
} log_fields_t;

// Internal functions exposed only for access by macros. Their
// real doxygen can be found in log.c.
/**
 * Implementation detail.
 */
void base_log_internal_core(log_severity_t severity, const char *file_name,
                            uint32_t line, const char *format, ...);
/**
 * Implementation detail.
 */
void base_log_internal_dv(const log_fields_t *log, int nargs, ...);

/**
 * Basic logging macro that all other logging macros delegate to.
 *
 * Prefer to use a LOG function with a specified severity, instead.
 *
 * @param _severity a severity of type `log_severity_t`.
 * @param _format a format string, as described in print.h. This must be a
 * string literal.
 * @param ... format parameters matching the format string.
 */
// Currently, this simply prints directly to printf. In the future, when
// we begin supporting DV testbenches, we can include an `if` statement here
// that detects that using `device.h` and switches to the cheaper "dump args
// for post process formatting" function.
//
// NOTE: the ##__VA_ARGS__ syntax below is a GCC/Clang extension, while
// "" foo "" is a common C idiom to assert that a macro parameter is a string.
#define LOG(_severity, _format, ...)                                          \
  do {                                                                        \
    if (kDeviceType == kDeviceSimDV) {                                        \
      /* Put the file name in the throw away .logs.strings section. */        \
      __attribute__(                                                          \
          (section(".logs.strings"))) static const char kFileNameStr[] =      \
          "" __FILE__ "";                                                     \
      /* Construct the log fields in the throw away .logs.fields section. */  \
      __attribute__(                                                          \
          (section(".logs.fields"))) static const log_fields_t kLogFields = { \
          .severity = _severity,                                              \
          .file_name = kFileNameStr,                                          \
          .line = __LINE__,                                                   \
          .nargs = GET_NUM_VARIABLE_ARGS(_format, ##__VA_ARGS__),             \
          .format = "" _format ""};                                           \
      base_log_internal_dv(&kLogFields,                                       \
                           GET_NUM_VARIABLE_ARGS(_format, ##__VA_ARGS__),     \
                           ##__VA_ARGS__);                                    \
    } else {                                                                  \
      base_log_internal_core(_severity, __FILE__, __LINE__, "" _format "",    \
                             _format, ##__VA_ARGS__);                         \
    }                                                                         \
  } while (false)

/**
 * Log an informational message.
 *
 * @param severity a severity of type `log_severity_t`.
 * @param format a format string, as described in print.h. This must be a string
 * literal.
 * @param ... format parameters matching the format string.
 */
#define LOG_INFO(...) LOG(kLogSeverityInfo, __VA_ARGS__)

/**
 * Log a warning
 *
 * @param severity a severity of type `log_severity_t`.
 * @param format a format string, as described in print.h. This must be a string
 * literal.
 * @param ... format parameters matching the format string.
 */
#define LOG_WARNING(...) LOG(kLogSeverityWarn, __VA_ARGS__)

/**
 * Log a non-fatal error.
 *
 * @param severity a severity of type `log_severity_t`.
 * @param format a format string, as described in print.h. This must be a string
 * literal.
 * @param ... format parameters matching the format string.
 */
#define LOG_ERROR(...) LOG(kLogSeverityError, __VA_ARGS__)

/**
 * Log a fatal error.
 *
 * @param severity a severity of type `log_severity_t`.
 * @param format a format string, as described in print.h. This must be a string
 * literal.
 * @param ... format parameters matching the format string.
 *
 * It is the user's responsibility to follow this up with a call to `abort()` to
 * immediately stop the execution.
 */
#define LOG_FATAL(...) LOG(kLogSeverityFatal, __VA_ARGS__)

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_LOG_H_
