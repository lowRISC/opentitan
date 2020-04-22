// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/log.h"

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/print.h"

/**
 * Ensure that log_fields_t is always 20 bytes.
 *
 * The assertion below helps prevent inadvertant changes to the struct.
 * Please see the description of log_fields_t in log.h for more details.
 */
_Static_assert(sizeof(log_fields_t) == 20,
               "log_fields_t must always be 20 bytes.");

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
    case kLogSeverityFatal:
      return "F";
    default:
      return "?";
  }
}

/**
 * Logs `log` and the values that follow to stdout.
 *
 * @param log the log data to log.
 * @param ... format parameters matching the format string.
 */
void base_log_internal_core(log_fields_t log, ...) {
  size_t file_name_len =
      ((char *)memchr(log.file_name, '\0', PTRDIFF_MAX)) - log.file_name;
  const char *base_name = memrchr(log.file_name, '/', file_name_len);
  if (base_name == NULL) {
    base_name = log.file_name;
  } else {
    ++base_name;  // Remove the final '/'.
  }

  // A small global counter that increments with each log line. This can be
  // useful for seeing how many times this function has been called, even if
  // nothing was printed for some time.
  static uint16_t global_log_counter = 0;

  base_printf("%s%5d %s:%d] ", stringify_severity(log.severity),
              global_log_counter, base_name, log.line);
  ++global_log_counter;

  va_list args;
  va_start(args, log);
  base_vprintf(log.format, args);
  va_end(args);

  base_printf("\r\n");
}

/**
 * Indicates the fixed location in RAM for SW logging for DV.
 * TODO: Figure aout a better place to put this.
 */
static const uintptr_t kSwDvLogAddr = 0x1000fffc;

/**
 * Logs `log and the values that follow in an efficient, DV-testbench
 * specific way.
 *
 * @param log a pointer to log data to log. Note that this pointer is likely to
 *        be invalid at runtime, since the pointed-to data will have been
 *        stripped from the binary.
 * @param nargs the number of arguments passed to the format string.
 * @param ... format parameters matching the format string.
 */
void base_log_internal_dv(const log_fields_t *log, uint32_t nargs, ...) {
  mmio_region_t log_device = mmio_region_from_addr(kSwDvLogAddr);
  mmio_region_write32(log_device, 0x0, (uintptr_t)log);

  va_list args;
  va_start(args, nargs);
  for (int i = 0; i < nargs; ++i) {
    mmio_region_write32(log_device, 0x0, va_arg(args, uint32_t));
  }
  va_end(args);
}
