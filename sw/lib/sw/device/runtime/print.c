// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/runtime/print.h"

#include <stdarg.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/dif/dif_uart.h"

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
  kHexLeLow = 'y',
  kHexLeHigh = 'Y',
  kStatusResult = 'r',
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
    .data = NULL,
    // Note: Using `&base_dev_null` causes this variable to be placed in the
    // .data section and triggers the assertion in rom.ld.
    .sink = NULL,
};

void base_set_stdout(buffer_sink_t out) {
  if (out.sink == NULL) {
    out.sink = &base_dev_null;
  }
  base_stdout = out;
}

static const size_t kSpiDeviceFrameHeaderSizeBytes = 12;
static uint32_t spi_device_frame_num = 0;

/**
 * Sends data out of the SPI device.
 *
 * Data is packaged into a frame that is described below. Note, the 0xFF padding
 * is to account for packet loss on the host side due to shortcomings in the
 * HyperDebug firmware. The host side reads the header first, then decides how
 * many words to read from the data section.
 *
 * -----------------------------------------------
 * |   0xFF_FF_FF_FF Pad   | 4-bytes  |          |
 * -----------------------------------|          |
 * |      Frame Number     | 4-bytes  |  Header  |
 * -----------------------------------|          |
 * |   Data Length (bytes) | 4-bytes  |          |
 * -----------------------------------|----------|
 * |   0xFF_FF_FF_FF Pad   | 4-bytes  |          |
 * -----------------------------------|          |
 * |      Data (word aligned)         |   Data   |
 * -----------------------------------|          |
 * |     0xFF Pad Bytes    | <4-bytes |          |
 * -----------------------------------|----------|
 */
static size_t base_dev_spi_device(void *data, const char *buf, size_t len) {
  dif_spi_device_handle_t *spi_device = (dif_spi_device_handle_t *)data;

  const size_t kDataPacketSizeBytes = ((len + 3u) & ~3u) + 4;
  const size_t kFrameSizeBytes =
      kSpiDeviceFrameHeaderSizeBytes + kDataPacketSizeBytes;
  uint8_t frame_bytes[kFrameSizeBytes];

  // Construct the frame header packet.
  // Add the pad bytes.
  for (size_t i = 0; i < 4; ++i) {
    frame_bytes[i] = 0xff;
  }
  // Add the frame number.
  for (size_t i = 0; i < 4; ++i) {
    frame_bytes[i + 4] = (spi_device_frame_num >> (i * 8)) & 0xff;
  }
  // Add the data length.
  for (size_t i = 0; i < 4; ++i) {
    frame_bytes[i + 8] = (len >> (i * 8)) & 0xff;
  }

  // Construct the frame data packet.
  // Add the pad bytes.
  for (size_t i = 0; i < 4; ++i) {
    frame_bytes[i + 12] = 0xff;
  }
  // Add the data and pad bytes.
  for (size_t i = 0; i < ((len + 3u) & ~3u); ++i) {
    if (i < len) {
      frame_bytes[i + 16] = buf[i];
    } else {
      frame_bytes[i + 16] = 0xff;
    }
  }

  // Send the frame.
  if (dif_spi_device_send_polled(spi_device, frame_bytes,
                                 /*buf_len=*/kFrameSizeBytes) != kDifOk) {
    return 0;
  }
  spi_device_frame_num++;

  return len;
}

static size_t base_dev_uart(void *data, const char *buf, size_t len) {
  const dif_uart_t *uart = (const dif_uart_t *)data;
  for (size_t i = 0; i < len; ++i) {
    if (dif_uart_byte_send_polled(uart, (uint8_t)buf[i]) != kDifOk) {
      return i;
    }
  }
  return len;
}

void base_spi_device_stdout(const dif_spi_device_handle_t *spi_device) {
  // Reset the frame counter.
  spi_device_frame_num = 0;
  base_set_stdout((buffer_sink_t){.data = (void *)spi_device,
                                  .sink = &base_dev_spi_device});
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
      .buf = buf,
      .bytes_left = len,
  };
  buffer_sink_t out = {
      .data = &data,
      .sink = &snprintf_sink,
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
  char padding;
  bool is_nonstd;
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

  // Parse a ! to detect an OpenTitan-specific extension (that isn't one
  // of the Verilog ones...).
  if ((*format)[0] == '!') {
    spec->is_nonstd = true;
    ++(*format);
  }

  // Attempt to parse out an unsigned, decimal number, a "width",
  // after the percent sign; the format specifier is the character
  // immediately after this width.
  //
  // `spec->padding` is used to indicate whether we've seen a width;
  // if nonzero, we have an actual width.
  size_t spec_len = 0;
  while (true) {
    char c = (*format)[spec_len];
    if (c == '\0') {
      *bytes_written += out.sink(out.data, kErrorNul, sizeof(kErrorNul));
      return false;
    }
    if (c < '0' || c > '9') {
      break;
    }
    if (spec->padding == 0) {
      if (c == '0') {
        spec->padding = '0';
        ++spec_len;
        continue;
      }
      spec->padding = ' ';
    }
    spec->width *= 10;
    spec->width += (c - '0');
    ++spec_len;
  }

  if ((spec->width == 0 && spec->padding != 0) || spec->width > 32) {
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
                           char padding, uint32_t base, const char *glyphs) {
  // All allocations are done relative to a buffer that could hold the longest
  // textual representation of a number: ~0x0 in base 2, i.e., 32 ones.
  static const int kWordBits = sizeof(uint32_t) * 8;
  char buffer[kWordBits];

  size_t len = 0;
  if (value == 0) {
    buffer[kWordBits - 1] = glyphs[0];
    ++len;
  }
  while (value > 0) {
    uint32_t digit = value % base;
    value /= base;
    buffer[kWordBits - 1 - len] = glyphs[digit];
    ++len;
  }
  width = width == 0 ? 1 : width;
  width = width > kWordBits ? kWordBits : width;
  while (len < width) {
    buffer[kWordBits - len - 1] = padding;
    ++len;
  }
  return out.sink(out.data, buffer + (kWordBits - len), len);
}

static size_t write_status(buffer_sink_t out, status_t value, bool as_json) {
  // The module id is defined to be 3 chars long.
  char mod[] = {'"', 0, 0, 0, '"', ','};
  int32_t arg;
  const char *start;
  bool err = status_extract(value, &start, &arg, &mod[1]);

  // strlen of the status code.
  const char *end = start;
  while (*end)
    end++;
  size_t len = 0;

  len += out.sink(out.data, "{\"", as_json ? 2 : 0);
  len += out.sink(out.data, start, (size_t)(end - start));
  len += out.sink(out.data, "\"", as_json ? 1 : 0);

  len += out.sink(out.data, ":", 1);
  if (err) {
    // All error codes include the module identifier.
    len += out.sink(out.data, "[", 1);
    len += out.sink(out.data, mod, sizeof(mod));
    len += write_digits(out, (uint32_t)arg, 0, 0, 10, kDigitsLow);
    len += out.sink(out.data, "]", 1);
  } else {
    // Ok codes include only the arg
    len += write_digits(out, (uint32_t)arg, 0, 0, 10, kDigitsLow);
  }
  len += out.sink(out.data, "}", as_json ? 1 : 0);
  return len;
}

/**
 * Hexdumps `bytes` onto `out`.
 *
 * @param out the sink to write bytes to.
 * @param bytes the bytes to dump.
 * @param len the number of bytes to dump.
 * @param width the minimum width to print; going below will result in writing
 *        out zeroes.
 * @param padding the character to use for padding.
 * @param big_endian whether to print in big-endian order (i.e. as %x would).
 * @param glyphs an array of characters to use as the digits of a number, which
 *        should be at least ast long as `base`.
 * @return the number of bytes written.
 */
static size_t hex_dump(buffer_sink_t out, const char *bytes, size_t len,
                       uint32_t width, char padding, bool big_endian,
                       const char *glyphs) {
  size_t bytes_written = 0;
  char buf[32];
  size_t buffered = 0;
  if (len < width) {
    width -= len;
    memset(buf, padding, sizeof(buf));
    while (width > 0) {
      size_t to_write = width > ARRAYSIZE(buf) ? 32 : width;
      bytes_written += out.sink(out.data, buf, to_write);
      width -= to_write;
    }
  }

  for (size_t i = 0; i < len; ++i) {
    size_t idx = big_endian ? len - i - 1 : i;
    buf[buffered] = glyphs[(bytes[idx] >> 4) & 0xf];
    buf[buffered + 1] = glyphs[bytes[idx] & 0xf];
    buffered += 2;

    if (buffered == ARRAYSIZE(buf)) {
      bytes_written += out.sink(out.data, buf, buffered);
      buffered = 0;
    }
  }

  if (buffered != 0) {
    bytes_written += out.sink(out.data, buf, buffered);
  }
  return bytes_written;
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
 * @param args the list to pull an entry from.
 */
static void process_specifier(buffer_sink_t out, format_specifier_t spec,
                              size_t *bytes_written, va_list *args) {
  // Switch on the specifier. At this point, we assert that there is
  // an initialized value of correct type in the VA list; if it is
  // missing, the caller has caused UB.
  switch (spec.type) {
    case kPercent: {
      if (spec.is_nonstd) {
        goto bad_spec;
      }
      *bytes_written += out.sink(out.data, "%", 1);
      break;
    }
    case kCharacter: {
      if (spec.is_nonstd) {
        goto bad_spec;
      }
      char value = (char)va_arg(*args, uint32_t);
      *bytes_written += out.sink(out.data, &value, 1);
      break;
    }
    case kString: {
      size_t len = 0;
      if (spec.is_nonstd) {
        // This implements %!s.
        len = va_arg(*args, size_t);
      }

      char *value = va_arg(*args, char *);
      while (!spec.is_nonstd && value[len] != '\0') {
        // This implements %s.
        ++len;
      }

      *bytes_written += out.sink(out.data, value, len);
      break;
    }
    case kSignedDec1:
    case kSignedDec2: {
      if (spec.is_nonstd) {
        goto bad_spec;
      }
      uint32_t value = va_arg(*args, uint32_t);
      if (((int32_t)value) < 0) {
        *bytes_written += out.sink(out.data, "-", 1);
        value = -value;
      }
      *bytes_written +=
          write_digits(out, value, spec.width, spec.padding, 10, kDigitsLow);
      break;
    }
    case kUnsignedOct: {
      if (spec.is_nonstd) {
        goto bad_spec;
      }
      uint32_t value = va_arg(*args, uint32_t);
      *bytes_written +=
          write_digits(out, value, spec.width, spec.padding, 8, kDigitsLow);
      break;
    }
    case kPointer: {
      if (spec.is_nonstd) {
        goto bad_spec;
      }
      // Pointers are formatted as 0x<hex digits>, where the width is always
      // set to the number necessary to represent a pointer on the current
      // platform, that is, the size of uintptr_t in nybbles. For example, on
      // different architecutres the null pointer prints as
      // - rv32imc: 0x00000000 (four bytes, eight nybbles).
      // - amd64:   0x0000000000000000 (eight bytes, sixteen nybbles).
      *bytes_written += out.sink(out.data, "0x", 2);
      uintptr_t value = va_arg(*args, uintptr_t);
      *bytes_written +=
          write_digits(out, value, sizeof(uintptr_t) * 2, '0', 16, kDigitsLow);
      break;
    }
    case kUnsignedHexLow:
      if (spec.is_nonstd) {
        size_t len = va_arg(*args, size_t);
        char *value = va_arg(*args, char *);
        *bytes_written += hex_dump(out, value, len, spec.width, spec.padding,
                                   /*big_endian=*/true, kDigitsLow);
        break;
      }
      OT_FALLTHROUGH_INTENDED;
    case kSvHexLow: {
      uint32_t value = va_arg(*args, uint32_t);
      *bytes_written +=
          write_digits(out, value, spec.width, spec.padding, 16, kDigitsLow);
      break;
    }
    case kUnsignedHexHigh:
      if (spec.is_nonstd) {
        size_t len = va_arg(*args, size_t);
        char *value = va_arg(*args, char *);
        *bytes_written += hex_dump(out, value, len, spec.width, spec.padding,
                                   /*big_endian=*/true, kDigitsHigh);
        break;
      }
      OT_FALLTHROUGH_INTENDED;
    case kSvHexHigh: {
      uint32_t value = va_arg(*args, uint32_t);
      *bytes_written +=
          write_digits(out, value, spec.width, spec.padding, 16, kDigitsHigh);
      break;
    }
    case kHexLeLow: {
      if (!spec.is_nonstd) {
        goto bad_spec;
      }
      size_t len = va_arg(*args, size_t);
      char *value = va_arg(*args, char *);
      *bytes_written += hex_dump(out, value, len, spec.width, spec.padding,
                                 /*big_endian=*/false, kDigitsLow);
      break;
    }
    case kHexLeHigh: {
      if (!spec.is_nonstd) {
        goto bad_spec;
      }
      size_t len = va_arg(*args, size_t);
      char *value = va_arg(*args, char *);
      *bytes_written += hex_dump(out, value, len, spec.width, spec.padding,
                                 /*big_endian=*/false, kDigitsHigh);
      break;
    }
    case kUnsignedDec: {
      if (spec.is_nonstd) {
        goto bad_spec;
      }
      uint32_t value = va_arg(*args, uint32_t);
      *bytes_written +=
          write_digits(out, value, spec.width, spec.padding, 10, kDigitsLow);
      break;
    }
    case kSvBinary: {
      if (spec.is_nonstd) {
        // Bools passed into a ... function will be automatically promoted
        // to int; va_arg(..., bool) is actually UB!
        if (va_arg(*args, int) != 0) {
          *bytes_written += out.sink(out.data, "true", 4);
        } else {
          *bytes_written += out.sink(out.data, "false", 5);
        }
        break;
      }
      uint32_t value = va_arg(*args, uint32_t);
      *bytes_written +=
          write_digits(out, value, spec.width, spec.padding, 2, kDigitsLow);
      break;
    }
    case kStatusResult: {
      status_t value = va_arg(*args, status_t);
      *bytes_written += write_status(out, value, spec.is_nonstd);
      break;
    }
    bad_spec:  // Used with `goto` to bail out early.
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

const char kBaseHexdumpDefaultFmtAlphabet[256] =
    // clang-format off
  // First 32 characters are not printable.
  "................................"
  // Printable ASCII.
  " !\"#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~"
  // The rest of the range is also not printable (129 characters).
  "................................................................"
  "................................................................"
  ".";
// clang-format on

static const base_hexdump_fmt_t kBaseHexdumpDefaultFmt = {
    .bytes_per_word = 2,
    .words_per_line = 8,
    .alphabet = &kBaseHexdumpDefaultFmtAlphabet,
};

size_t base_hexdump(const char *buf, size_t len) {
  return base_hexdump_with(kBaseHexdumpDefaultFmt, buf, len);
}

size_t base_snhexdump(char *out, size_t out_len, const char *buf, size_t len) {
  return base_snhexdump_with(out, out_len, kBaseHexdumpDefaultFmt, buf, len);
}

size_t base_fhexdump(buffer_sink_t out, const char *buf, size_t len) {
  return base_fhexdump_with(out, kBaseHexdumpDefaultFmt, buf, len);
}

size_t base_hexdump_with(base_hexdump_fmt_t fmt, const char *buf, size_t len) {
  return base_fhexdump_with(base_stdout, fmt, buf, len);
}

size_t base_snhexdump_with(char *out, size_t out_len, base_hexdump_fmt_t fmt,
                           const char *buf, size_t len) {
  snprintf_captures_t data = {
      .buf = out,
      .bytes_left = out_len,
  };
  buffer_sink_t sink = {
      .data = &data,
      .sink = &snprintf_sink,
  };
  return base_fhexdump_with(sink, fmt, buf, len);
}

size_t base_fhexdump_with(buffer_sink_t out, base_hexdump_fmt_t fmt,
                          const char *buf, size_t len) {
  size_t bytes_written = 0;
  size_t bytes_per_line = fmt.bytes_per_word * fmt.words_per_line;

  for (size_t line = 0; line < len; line += bytes_per_line) {
    bytes_written += base_fprintf(out, "%08x:", line);

    size_t chars_per_line = bytes_per_line * 2 + fmt.words_per_line;
    size_t line_bytes_written = 0;
    for (size_t word = 0; word < bytes_per_line; word += fmt.bytes_per_word) {
      if (len < line + word) {
        char spaces[16] = "                ";
        while (line_bytes_written < chars_per_line) {
          size_t to_print = chars_per_line - line_bytes_written;
          if (to_print > sizeof(spaces)) {
            to_print = sizeof(spaces);
          }
          line_bytes_written += base_fprintf(out, "%!s", to_print, spaces);
        }
        break;
      }

      size_t bytes_left = len - line - word;
      if (bytes_left > fmt.bytes_per_word) {
        bytes_left = fmt.bytes_per_word;
      }
      line_bytes_written += base_fprintf(out, " ");
      line_bytes_written +=
          hex_dump(out, buf + line + word, bytes_left, bytes_left, '0',
                   /*big_endian=*/false, kDigitsLow);
    }
    bytes_written += line_bytes_written;

    bytes_written += base_fprintf(out, "  ");
    size_t buffered = 0;
    char glyph_buffer[16];
    for (size_t byte = 0; byte < bytes_per_line; ++byte) {
      if (buffered == sizeof(glyph_buffer)) {
        bytes_written += base_fprintf(out, "%!s", buffered, glyph_buffer);
        buffered = 0;
      }
      if (line + byte >= len) {
        break;
      }
      glyph_buffer[buffered++] =
          (*fmt.alphabet)[(size_t)(uint8_t)buf[line + byte]];
    }
    if (buffered > 0) {
      bytes_written += base_fprintf(out, "%!s", buffered, glyph_buffer);
    }
    bytes_written += base_fprintf(out, "\n");
  }

  return bytes_written;
}
