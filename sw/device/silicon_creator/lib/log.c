// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/log.h"

#include <assert.h>
#include <stdarg.h>
#include <stdint.h>

#include "sw/device/silicon_creator/lib/drivers/uart.h"

rom_error_t log_printf(const char *format, ...) {
  va_list args;
  va_start(args, format);

  while (*format != '\0') {
    if (*format == '%') {
      ++format;
      switch (*format++) {
        case 's': {
          // Print a null-terminated string.
          const char *str = va_arg(args, const char *);
          while (*str != '\0') {
            uart_putchar(*str++);
          }
          continue;
        }
        case 'x': {
          // Print an `unsigned int` in hexadecimal.
          const char kHexTable[16] = "0123456789abcdef";
          unsigned int v = va_arg(args, unsigned int);
          static_assert(sizeof(unsigned int) == 4,
                        "sizeof(unsigned int) is not 4");
          for (int32_t i = 28; i >= 0; i -= 4) {
            uart_putchar(kHexTable[(v >> i) & 0xf]);
          }
          continue;
        }
        default:
          return kErrorLogBadFormatSpecifier;
      }
    }
    uart_putchar(*format++);
  }

  va_end(args);
  return kErrorOk;
}
