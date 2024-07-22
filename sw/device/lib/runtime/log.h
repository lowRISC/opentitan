// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_RUNTIME_LOG_H_
#define OPENTITAN_SW_DEVICE_LIB_RUNTIME_LOG_H_

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"

/**
 * @file
 * @brief Generic logging APIs
 *
 * The logging APIs below take a format string with a variable number of
 * arguments for the type specifiers. The APIs are designed to provide a way
 * for attaching the log severity, file name, and line number
 * information along with the message to provide an easier path to debug.
 * These parameters form a log prefix, which is prepended to the actual
 * message being printed. The following is a brief description of these:
 *
 *  log_type:     Severity of the message: info, warning, error or fatal
 *
 *  file name:    Name of the file using __FILE__
 *
 *  line number:  Line where the print originated using __LINE__
 *
 * Log macros support OpenTitan formatting specifiers; see print.h for
 * details the subset of C specifier syntax supported.
 *
 * The precise mechanism for logging is dependent on the target device. On core
 * devices, like Verilator, logs are printed using whatever `stdout` is set to
 * in print.h. DV testbenches may use an alternative, more efficient mechanism.
 *
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
 * Represents log metadata used to format a log line.
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
   * Indicates the severity of the LOG.
   */
  log_severity_t severity;
  /**
   * Name of the file at which a LOG line occurs, e.g. `__FILE__`. There
   * are no requirements for this string, other than that it be some kind of
   * UNIX-like pathname.
   */
  const char *file_name;
  /**
   * Indicates the line number at which the LOG line occurs, e.g., `__LINE__`.
   */
  uint32_t line;
  /**
   * Indicates the number of arguments passed to the format string.
   *
   * This value used only in DV mode, and is ignored by non-DV logging.
   */
  uint32_t nargs;
  /**
   * The actual format string.
   */
  const char *format;
} log_fields_t;

// Internal functions exposed only for access by macros. Their
// real doxygen can be found in log.c.
/**
 * Implementation detail.
 */
void base_log_internal_core(log_fields_t log, ...);
/**
 * Implementation detail.
 */
void base_log_internal_dv(const log_fields_t *log, uint32_t nargs, ...);

extern char _dv_log_offset[];

/**
 * A macro that wraps the `OT_FAIL_IF_64_BIT` macro, providing the name
 * of the LOG macro for better error messages.
 *
 * @param arg an arg/expression to check
 */
#define OT_FAIL_IF_64_BIT_LOG(arg) OT_FAIL_IF_64_BIT(arg, LOG)

/**
 * A macro that checks the variable arguments of the `LOG` function are valid
 * at compile time, by asserting that each of the argument is not a standard
 * C integer type with a width of 64 bits. Any such invalid argument will
 * cause a relevant error via a static assertion.
 *
 * @param ... the variable args list
 */
#define OT_CHECK_VALID_LOG_ARGS(...) \
  OT_VA_FOR_EACH(OT_FAIL_IF_64_BIT_LOG, ##__VA_ARGS__)

/**
 * Basic logging macro that all other logging macros delegate to.
 *
 * Prefer to use a LOG function with a specified severity, instead.
 *
 * @param severity a severity of type `log_severity_t`.
 * @param format a format string, as described in print.h. This must be a
 *               string literal.
 * @param ... format parameters matching the format string.
 */
#define LOG(severity, format, ...)                               \
  do {                                                           \
    OT_CHECK_VALID_LOG_ARGS(__VA_ARGS__);                        \
    if (kDeviceLogBypassUartAddress != 0) {                      \
      /* clang-format off */                                     \
      /* Put DV-only log constants in .logs.* sections, which
       * the linker will dutifully discard.
       * Unfortunately, clang-format really mangles these
       * declarations, so we format them manually. */            \
      __attribute__((section(".logs.fields")))                   \
      static const log_fields_t kLogFields =                     \
          LOG_MAKE_FIELDS_(severity, format, ##__VA_ARGS__);     \
      base_log_internal_dv((const log_fields_t*)((char*)&kLogFields + (uintptr_t)&_dv_log_offset), \
                           OT_VA_ARGS_COUNT(format, ##__VA_ARGS__), \
                           ##__VA_ARGS__); /* clang-format on */ \
    } else {                                                     \
      log_fields_t log_fields =                                  \
          LOG_MAKE_FIELDS_(severity, format, ##__VA_ARGS__);     \
      base_log_internal_core(log_fields, ##__VA_ARGS__);         \
    }                                                            \
  } while (false)

/**
 * Implementation detail of `LOG`.
 */
#define LOG_MAKE_FIELDS_(_severity, _format, ...)                         \
  {                                                                       \
    .severity = _severity, .file_name = "" __FILE__ "", .line = __LINE__, \
    .nargs = OT_VA_ARGS_COUNT(_format, ##__VA_ARGS__), .format = _format, \
  }

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

#endif  // OPENTITAN_SW_DEVICE_LIB_RUNTIME_LOG_H_
