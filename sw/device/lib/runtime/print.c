// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/runtime/print.h"

#include <stdarg.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/memory.h"

// This is declared as an enum to force the values to be
// compile-time constants, but the type is otherwise not
// used for anything.
enum {
  // Standard format specifiers.
  kPercent = '%',
  kCharacter = 'c',
  kString = 's',
  kSignedDec1 = 'd',
  kSignedDec2 = 'i',
  kUnsignedOct = 'o',
  kUnsignedHexLow = 'x',
  kUnsignedHexHigh = 'X',
  kUnsignedDec = 'u',
  kPointer = 'p',

  // Verilog-style format specifiers.
  kSvBinary = 'b',
  kSvHexLow = 'h',
  kSvHexHigh = 'H',

  // Other non-standard specifiers.
  kSizedStr = 'z',
};

// NOTE: all of the lengths of the strings below are given so that the NUL
// terminator is left off; that way, `sizeof(kConst)` does not include it.
static const char kDigitsLow[16] = "0123456789abcdef";
static const char kDigitsHigh[16] = "0123456789ABCDEF";

static const char kErrorNul[17] = "%<unexpected nul>";
static const char kUnknownSpec[15] = "%<unknown spec>";
static const char kErrorTooWide[12] = "%<bad width>";

static size_t base_dev_null(void *data, const char *buf, size_t len) {
  return len;
}
static buffer_sink_t base_stdout = {
    .data = NULL, .sink = &base_dev_null,
};

void base_set_stdout(buffer_sink_t out) {
  if (out.sink == NULL) {
    out.sink = &base_dev_null;
  }
  base_stdout = out;
}

static size_t base_dev_uart(void *data, const char *buf, size_t len) {
  const dif_uart_t *uart = (const dif_uart_t *)data;
  for (size_t i = 0; i < len; ++i) {
    if (dif_uart_byte_send_polled(uart, (uint8_t)buf[i]) != kDifUartOk) {
      return i;
    }
  }
  return len;
}

void base_uart_stdout(const dif_uart_t *uart) {
  base_set_stdout(
      (buffer_sink_t){.data = (void *)uart, .sink = &base_dev_uart});
}

size_t base_printf(const char *format, ...) {
  va_list args;
  va_start(args, format);
  size_t bytes_left = base_vprintf(format, args);
  va_end(args);
  return bytes_left;
}

size_t base_vprintf(const char *format, va_list args) {
  return base_vfprintf(base_stdout, format, args);
}

typedef struct snprintf_captures_t {
  char *buf;
  size_t bytes_left;
} snprintf_captures_t;

static size_t snprintf_sink(void *data, const char *buf, size_t len) {
  snprintf_captures_t *captures = (snprintf_captures_t *)data;
  if (captures->bytes_left == 0) {
    return 0;
  }

  if (len > captures->bytes_left) {
    len = captures->bytes_left;
  }
  memcpy(captures->buf, buf, len);
  captures->buf += len;
  captures->bytes_left -= len;
  return len;
}

size_t base_snprintf(char *buf, size_t len, const char *format, ...) {
  va_list args;
  va_start(args, format);

  snprintf_captures_t data = {
      .buf = buf, .bytes_left = len,
  };
  buffer_sink_t out = {
      .data = &data, .sink = &snprintf_sink,
  };
  size_t bytes_left = base_vfprintf(out, format, args);
  va_end(args);
  return bytes_left;
}

size_t base_fprintf(buffer_sink_t out, const char *format, ...) {
  va_list args;
  va_start(args, format);
  size_t bytes_left = base_vfprintf(out, format, args);
  va_end(args);
  return bytes_left;
}

/**
 * Consumes characters from `format` until a '%' or NUL is reached. All
 * characters seen before that are then sinked into `out`.
 *
 * @param out the sink to write bytes to.
 * @param format a pointer to the format string to consume a prefix of.
 * @param[out] bytes_written out param for the number of bytes writen to `out`.
 * @return true if an unprocessed '%' was found.
 */
static bool consume_until_percent(buffer_sink_t out, const char **format,
                                  size_t *bytes_written) {
  size_t text_len = 0;
  while (true) {
    char c = (*format)[text_len];
    if (c == '\0' || c == kPercent) {
      if (text_len > 0) {
        *bytes_written += out.sink(out.data, *format, text_len);
      }
      *format += text_len;
      return c != '\0';
    }
    ++text_len;
  }
}

/**
 * Represents a parsed format specifier.
 */
typedef struct format_specifier {
  char type;
  size_t width;
} format_specifier_t;

/**
 * Consumes characters from `format` until a complete format specifier is
 * parsed. See the documentation in `print.h` for full syntax.
 *
 * @param out the sink to write bytes to.
 * @param format a pointer to the format string to consume a prefix of.
 * @param[out] spec out param for the specifier.
 * @return whether the parse succeeded.
 */
static bool consume_format_specifier(buffer_sink_t out, const char **format,
                                     size_t *bytes_written,
                                     format_specifier_t *spec) {
  *spec = (format_specifier_t){0};

  // Consume the percent sign.
  ++(*format);

  // Attempt to parse out an unsigned, decimal number, a "width",
  // after the percent sign; the format specifier is the character
  // immediately after this width.
  size_t spec_len = 0;
  bool has_width = false;
  while (true) {
    char c = (*format)[spec_len];
    if (c == '\0') {
      *bytes_written += out.sink(out.data, kErrorNul, sizeof(kErrorNul));
      return false;
    }
    if (c < '0' || c > '9') {
      break;
    }
    has_width = true;
    spec->width *= 10;
    spec->width += (c - '0');
    ++spec_len;
  }

  if ((spec->width == 0 && has_width) || spec->width > 32) {
    *bytes_written += out.sink(out.data, kErrorTooWide, sizeof(kErrorTooWide));
    return false;
  }

  spec->type = (*format)[spec_len];
  *format += spec_len + 1;
  return true;
}

/**
 * Write the digits of `value` onto `out`.
 *
 * @param out the sink to write bytes to.
 * @param value the value to "stringify".
 * @param width the minimum width to print; going below will result in writing
 *        out zeroes.
 * @param base the base to express `value` in.
 * @param glyphs an array of characters to use as the digits of a number, which
 *        should be at least ast long as `base`.
 * @return the number of bytes written.
 */
static size_t write_digits(buffer_sink_t out, uint32_t value, uint32_t width,
                           uint32_t base, const char *glyphs) {
  // All allocations are done relative to a buffer that could hold the longest
  // textual representation of a number: ~0x0 in base 2, i.e., 32 ones.
  static const int kWordBits = sizeof(uint32_t) * 8;
  char buffer[kWordBits];

  size_t len = 0;
  while (value > 0) {
    uint32_t digit = value % base;
    value /= base;
    buffer[kWordBits - 1 - len] = glyphs[digit];
    ++len;
  }
  width = width == 0 ? 1 : width;
  width = width > kWordBits ? kWordBits : width;
  while (len < width) {
    buffer[kWordBits - len - 1] = '0';
    ++len;
  }
  return out.sink(out.data, buffer + (kWordBits - len), len);
}

/**
 * Prints out the next entry in `args` according to `spec`.
 *
 * This function assumes that `spec` accurately describes the next entry in
 * `args`.
 *
 * @param out the sink to write bytes to.
 * @param spec the specifier to use for stringifying.
 * @param[out] bytes_written out param for the number of bytes writen to `out`.
 * @param va_list the list to pull an entry from.
 */
static void process_specifier(buffer_sink_t out, format_specifier_t spec,
                              size_t *bytes_written, va_list *args) {
  // Switch on the specifier. At this point, we assert that there is
  // an initialized value of correct type in the VA list; if it is
  // missing, the caller has caused UB.
  switch (spec.type) {
    case kPercent: {
      *bytes_written += out.sink(out.data, "%", 1);
      break;
    }
    case kCharacter: {
      char value = (char)va_arg(*args, uint32_t);
      *bytes_written += out.sink(out.data, &value, 1);
      break;
    }
    case kString: {
      char *value = va_arg(*args, char *);
      size_t len = 0;
      while (value[len] != '\0') {
        ++len;
      }
      *bytes_written += out.sink(out.data, value, len);
      break;
    }
    case kSizedStr: {
      size_t len = va_arg(*args, size_t);
      char *value = va_arg(*args, char *);
      *bytes_written += out.sink(out.data, value, len);
      break;
    }
    case kSignedDec1:
    case kSignedDec2: {
      uint32_t value = va_arg(*args, uint32_t);
      if (((int32_t)value) < 0) {
        *bytes_written += out.sink(out.data, "-", 1);
        value = -value;
      }
      *bytes_written += write_digits(out, value, spec.width, 10, kDigitsLow);
      break;
    }
    case kUnsignedOct: {
      uint32_t value = va_arg(*args, uint32_t);
      *bytes_written += write_digits(out, value, spec.width, 8, kDigitsLow);
      break;
    }
    case kPointer: {
      // Pointers are formatted as 0x<hex digits>, where the width is always
      // set to the number necessary to represent a pointer on the current
      // platform, that is, the size of uintptr_t in nybbles. For example, on
      // different architecutres the null pointer prints as
      // - rv32imc: 0x00000000 (four bytes, eight nybbles).
      // - amd64:   0x0000000000000000 (eight bytes, sixteen nybbles).
      *bytes_written += out.sink(out.data, "0x", 2);
      uintptr_t value = va_arg(*args, uintptr_t);
      *bytes_written +=
          write_digits(out, value, sizeof(uintptr_t) * 2, 16, kDigitsLow);
      break;
    }
    case kSvHexLow:
    case kUnsignedHexLow: {
      uint32_t value = va_arg(*args, uint32_t);
      *bytes_written += write_digits(out, value, spec.width, 16, kDigitsLow);
      break;
    }
    case kSvHexHigh:
    case kUnsignedHexHigh: {
      uint32_t value = va_arg(*args, uint32_t);
      *bytes_written += write_digits(out, value, spec.width, 16, kDigitsHigh);
      break;
    }
    case kUnsignedDec: {
      uint32_t value = va_arg(*args, uint32_t);
      *bytes_written += write_digits(out, value, spec.width, 10, kDigitsLow);
      break;
    }
    case kSvBinary: {
      uint32_t value = va_arg(*args, uint32_t);
      *bytes_written += write_digits(out, value, spec.width, 2, kDigitsLow);
      break;
    }
    default: {
      *bytes_written += out.sink(out.data, kUnknownSpec, sizeof(kUnknownSpec));
    }
  }
}

size_t base_vfprintf(buffer_sink_t out, const char *format, va_list args) {
  if (out.sink == NULL) {
    out.sink = &base_dev_null;
  }

  // NOTE: This copy is necessary on amd64 and other platforms, where
  // `va_list` is a fixed array type (and, as such, decays to a pointer in
  // an argument list). On PSABI RV32IMC, however, `va_list` is a `void*`, so
  // this is a copy of the pointer, not the array.
  va_list args_copy;
  va_copy(args_copy, args);

  size_t bytes_written = 0;
  while (format[0] != '\0') {
    if (!consume_until_percent(out, &format, &bytes_written)) {
      break;
    }
    format_specifier_t spec;
    if (!consume_format_specifier(out, &format, &bytes_written, &spec)) {
      break;
    }

    process_specifier(out, spec, &bytes_written, &args_copy);
  }

  va_end(args_copy);
  return bytes_written;
}
