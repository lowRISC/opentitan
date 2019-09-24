// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "msg.h"

#include <stdarg.h>

static void _print_dec(void (*output)(char), unsigned int d) {
  output("0123456789ABCDEF"[d]);
}

static void _print_hex(void (*output)(char), unsigned int byte) {
  _print_dec(output, (byte >> 4) & 15);
  _print_dec(output, byte & 15);
}

static void _print_num(void (*output)(char), int w, unsigned int n,
                       unsigned int base) {
  if (--w > 0 || n >= base) {
    _print_num(output, w, n / base, base);
  }
  _print_dec(output, n % base);
}

void msg_print(void (*output)(char), const char *msg_header, const char *fmt,
               ...) {
  char ch;
  va_list va;

  while (*msg_header != '\0') {
    output(*msg_header++);
  }

  va_start(va, fmt);
  while ((ch = *fmt) != '\0') {
    ++fmt;
    if (ch != '%') {
      if (ch == '\n') {
        output('\r');
      }
      output(ch);
    } else {
      int w = 0;
      while ((ch = *fmt) != '\0') {
        ++fmt;
        if (ch >= '0' && ch <= '9') {
          w = w * 10 + (ch - '0');
          continue;
        } else {
          switch (ch) {
            case '\0':
            case '%': {
              output('%');
            } break;
            case 'd': {
              unsigned int n = va_arg(va, unsigned int);
              if ((int)n < 0) {
                output('-');
                n = -n;
              }
              _print_num(output, w, n, 10);
            } break;
            case 'x':
            case 'X': {
              unsigned int n = va_arg(va, unsigned int);
              if (ch == 'X') {
                w = 8;
                // TODO: fixme
                // n = bswap(n);
              }
              _print_num(output, w, n, 16);
            } break;
            case 'u': {
              unsigned int n = va_arg(va, unsigned int);
              _print_num(output, w, n, 10);
            } break;
            case 's': {
              const char *s = va_arg(va, const char *);
              while (*s) {
                output(*s++);
              }
            } break;
            case 'c': {
              char c = va_arg(va, int);
              output(c);
            } break;
            case 'h': {  // little endian hex dump
              int cnt = va_arg(va, int);
              unsigned char *p = va_arg(va, unsigned char *);
              while (cnt--) {
                _print_hex(output, *p++);
              }
            } break;
            case 'H': {  // big endian hex dump
              int cnt = va_arg(va, int);
              unsigned char *p = va_arg(va, unsigned char *);
              p += cnt;
              while (cnt--) {
                _print_hex(output, *--p);
              }
            } break;
            default: {  // unknown format
              output('%');
              output(ch);
            } break;
          }
          break;
        }
      }
    }
  }
  va_end(va);
}
