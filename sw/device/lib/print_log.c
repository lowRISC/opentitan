// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/print_log.h"

#include <stdarg.h>

// Identifiers for string format type specifiers.
static const char kFormatSpecifier = '%';
static const char kBinary = 'b';       // Print binary [SystemVerilog style].
static const char kDecimalI = 'i';     // Signed decimal.
static const char kDecimal = 'd';      // Signed decimal.
static const char kUnsigned = 'u';     // Unsigned decimal.
static const char kOctal = 'o';        // Octal.
static const char kAsciiChar = 'c';    // Single character byte.
static const char kHexUpper = 'X';     // Upper case hex.
static const char kHexAltUpper = 'H';  // Upper case hex [SystemVerilog style].
static const char kHexLower = 'x';     // Lower case hex.
static const char kHexAltLower = 'h';  // Lower case hex [SystemVerilog style].
static const char kPercent = '%';      // Escape '%'.

static inline void print_digit(print_char_func print_char, unsigned int digit) {
  print_char("0123456789ABCDEF"[digit]);
}

static inline void print_num(print_char_func print_char, int width,
                             unsigned int n, unsigned int base) {
  // TODO: Consider changing this to for loop.
  if (--width > 0 || n >= base) {
    print_num(print_char, width, n / base, base);
  }
  print_digit(print_char, n % base);
}

void print_log(print_char_func print_char, const char *fmt, ...) {
  va_list va;
  va_start(va, fmt);

  while (*fmt != '\0') {
    char ch = *fmt++;
    if (ch != kFormatSpecifier) {
      // Add CR to new line automatically (if not added already).
      if (ch == '\n' && !(*(fmt - 1) == '\r' || *(fmt + 1) == '\r')) {
        print_char('\r');
      }
      print_char(ch);
    } else {
      int w = 0;
      // TODO: Refactor this into a separate function.
      while (*fmt != '\0') {
        ch = *fmt++;
        // Parse width field.
        if (ch >= '0' && ch <= '9') {
          w = w * 10 + (ch - '0');
          continue;
        } else {
          switch (ch) {
            case '\0': {
              return;
            }
            case kBinary: {
              unsigned int n = va_arg(va, unsigned int);
              print_num(print_char, w, n, 2);
              break;
            }
            case kDecimalI:
            case kDecimal: {
              unsigned int n = va_arg(va, unsigned int);
              if (((int)n) < 0) {
                print_char('-');
                n = -n;
              }
              print_num(print_char, w, n, 10);
              break;
            }
            case kUnsigned: {
              unsigned int n = va_arg(va, unsigned int);
              print_num(print_char, w, n, 10);
              break;
            }
            case kOctal: {
              unsigned int n = va_arg(va, unsigned int);
              print_num(print_char, w, n, 8);
              break;
            }
            case kHexLower:
            case kHexAltLower:
            case kHexUpper:
            case kHexAltUpper: {
              // TODO: This will still print in upper case.
              unsigned int n = va_arg(va, unsigned int);
              print_num(print_char, w, n, 16);
              break;
            }
            case kAsciiChar: {
              char c = va_arg(va, int);
              print_char(c);
              break;
            }
            case kPercent: {
              print_char('%');
              break;
            }
            default: {
              // Unknown format - this error message is printed inline within
              // the message.
              print_log(print_char, "[INVALID SPECIFIER: %%%c]", ch);
              break;
            }
          }
          break;
        }
      }
    }
  }
  va_end(va);
}
