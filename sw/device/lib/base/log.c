// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/log.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/print.h"

/**
 * Converts a severity to a static string.
 */
static const char *stringify_severity(log_severity_t severity) {
  switch (severity) {
    case kLogSeverityInfo:
      return "I";
    case kLogSeverityWarn:
      return "W";
    case kLogSeverityError:
      return "E";
    default:
      return "?";
  }
}

/**
 * Logs |format| and the values that following to stdout.
 *
 * @param severity the log severity.
 * @param file_name a constant string referring to the file in which the log
 * occured.
 * @param line a line number from |file_name|.
 * @param format a format string, as described in print.h. This must be a string
 * literal.
 * @param ... format parameters matching the format string.
 */
void base_log_internal_core(log_severity_t severity, const char *file_name,
                            uint32_t line, const char *format, ...) {
  size_t file_name_len = ((char *)memchr(file_name, '\0', PTRDIFF_MAX)) - file_name;
  const char *base_name = memrchr(file_name, '/', file_name_len);
  if (base_name == NULL) {
    base_name = file_name;
  } else { 
    ++base_name;  // Remove the final '/'.
  }

  // A small global counter that increments with each log line. This can be useful for
  // seeing how many times this function has been called, even if nothing was printed
  // for some time.
  static uint16_t global_log_counter = 0;

  base_printf("%s%5d %s:%d] ", stringify_severity(severity), global_log_counter, base_name, line);
  ++global_log_counter;

  va_list args;
  va_start(args, format);
  base_vprintf(format, args);
  va_end(args);

  base_printf("\r\n");
}

/**
 * Logs |format| and the values that following in an efficient, DV-testbench
 * specific way.
 *
 * @param severity the log severity.
 * @param format a format string, as described in print.h. This must be a string
 * literal.
 * @param ... format parameters matching the format string.
 */
void base_log_internal_dv(log_severity_t severity, const char *format, ...) {
  // Do nothing, for now.
}