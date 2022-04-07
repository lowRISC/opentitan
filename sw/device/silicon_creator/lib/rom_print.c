// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/rom_print.h"

#include <assert.h>
#include <stdarg.h>
#include <stdint.h>

#include "sw/device/silicon_creator/lib/drivers/uart.h"

rom_error_t rom_printf(const char *format, ...) {
  va_list args;
  va_start(args, format);

  while (*format != '\0') {
    if (*format != '%') {
      uart_putchar(*format++);
      continue;
    }

    ++format;  // Skip over the '%'.
    switch (*format++) {
      case 's': {
        // Print a null-terminated string.
        const char *str = va_arg(args, const char *);
        while (*str != '\0') {
          uart_putchar(*str++);
        }
        break;
      }
      case 'x': {
        // Print an `unsigned int` in hexadecimal.
        static const char kHexTable[16] = "0123456789abcdef";
        unsigned int v = va_arg(args, unsigned int);
        for (int i = 0; i < sizeof(v) * 2; ++i) {
          int shift = sizeof(v) * 8 - 4;
          uart_putchar(kHexTable[v >> shift]);
          v <<= 4;
        }
        break;
      }
      default:
        va_end(args);
        return kErrorLogBadFormatSpecifier;
    }
  }

  va_end(args);
  return kErrorOk;
}
