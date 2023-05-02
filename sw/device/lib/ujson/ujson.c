// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/ujson/ujson.h"

#include <stdbool.h>
#include <stdint.h>
#include <string.h>

#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/ujson/private_status.h"
#include "sw/device/silicon_creator/lib/crc32.h"

static bool is_space(int c) { return c == ' ' || (unsigned)c - '\t' < 5; }

ujson_t ujson_init(void *context, status_t (*getc)(void *),
                   status_t (*putbuf)(void *, const char *, size_t)) {
  ujson_t u = UJSON_INIT(context, getc, putbuf);
  return u;
}

void ujson_crc32_reset(ujson_t *uj) { crc32_init(&uj->crc32); }

uint32_t ujson_crc32_finish(ujson_t *uj) { return crc32_finish(&uj->crc32); }

status_t ujson_putbuf(ujson_t *uj, const char *buf, size_t len) {
  crc32_add(&uj->crc32, buf, len);
  return uj->putbuf(uj->io_context, buf, len);
}

status_t ujson_getc(ujson_t *uj) {
  int16_t buffer = uj->buffer;
  if (buffer >= 0) {
    uj->buffer = -1;
    return OK_STATUS(buffer);
  } else {
    status_t s = uj->getc(uj->io_context);
    if (!status_err(s)) {
      crc32_add8(&uj->crc32, (uint8_t)s.value);
    }
    return s;
  }
}

status_t ujson_ungetc(ujson_t *uj, char ch) {
  if (uj->buffer >= 0) {
    return FAILED_PRECONDITION();
  }
  uj->buffer = ch;
  return OK_STATUS();
}

bool ujson_streq(const char *a, const char *b) {
  while (*a && *b && *a == *b) {
    ++a;
    ++b;
  }
  return *a == *b;
}

// Consumes whitespace returning first non-whitepsace character found.
static status_t consume_whitespace(ujson_t *uj) {
  int ch;
  do {
    ch = TRY(ujson_getc(uj));
  } while (is_space(ch));
  return OK_STATUS(ch);
}

static status_t consume_hexdigit(ujson_t *uj) {
  int ch = TRY(ujson_getc(uj));
  if (ch >= '0' && ch <= '9') {
    return OK_STATUS(ch - '0');
  } else if (ch >= 'A' && ch <= 'F') {
    return OK_STATUS(ch - 'A' + 10);
  } else if (ch >= 'a' && ch <= 'f') {
    return OK_STATUS(ch - 'a' + 10);
  } else {
    return OUT_OF_RANGE();
  }
}

static status_t consume_hex(ujson_t *uj) {
  int a = TRY(consume_hexdigit(uj));
  int b = TRY(consume_hexdigit(uj));
  int c = TRY(consume_hexdigit(uj));
  int d = TRY(consume_hexdigit(uj));
  return OK_STATUS((a << 12) | (b << 8) | (c << 4) | d);
}

status_t ujson_consume(ujson_t *uj, char ch) {
  if (ch != TRY(consume_whitespace(uj))) {
    return NOT_FOUND();
  }
  return OK_STATUS();
}

status_t ujson_consume_maybe(ujson_t *uj, char ch) {
  char got = (char)TRY(consume_whitespace(uj));
  if (ch != got) {
    ujson_ungetc(uj, got);
    return OK_STATUS(0);
  }
  return OK_STATUS(1);
}

status_t ujson_parse_qs(ujson_t *uj, char *str, size_t len) {
  char ch;
  int n = 0;
  len--;  // One char for the nul terminator.
  TRY(ujson_consume(uj, '"'));
  while (true) {
    ch = (char)TRY(ujson_getc(uj));
    if (ch == '\"')
      break;
    if (ch == '\\') {
      ch = (char)TRY(ujson_getc(uj));
      switch (ch) {
        case '"':
        case '\\':
        case '/':
          break;
        case 'b':
          ch = '\b';
          break;
        case 'f':
          ch = '\f';
          break;
        case 'n':
          ch = '\n';
          break;
        case 'r':
          ch = '\r';
          break;
        case 't':
          ch = '\t';
          break;
        case 'u':
          ch = (char)TRY(consume_hex(uj));
          break;
        default:
          return OUT_OF_RANGE();
      }
    }
    if (len > 0) {
      *str++ = ch;
      --len;
      n++;
    }
  }
  *str = '\0';
  return OK_STATUS(n);
}

status_t ujson_parse_integer(ujson_t *uj, void *result, size_t rsz) {
  char ch = (char)TRY(consume_whitespace(uj));
  bool neg = false;

  if (ch == '-') {
    neg = true;
    ch = (char)TRY(ujson_getc(uj));
  }
  int64_t value = 0;

  if (!(ch >= '0' && ch <= '9')) {
    return NOT_FOUND();
  }
  status_t s;
  while (ch >= '0' && ch <= '9') {
    value *= 10;
    value += ch - '0';
    s = ujson_getc(uj);
    if (status_err(s))
      break;
    ch = (char)s.value;
  }
  if (status_ok(s))
    TRY(ujson_ungetc(uj, ch));
  if (neg)
    value = -value;
  memcpy(result, &value, rsz);
  return OK_STATUS();
}

status_t ujson_deserialize_bool(ujson_t *uj, bool *value) {
  char got = (char)TRY(consume_whitespace(uj));
  if (got == 't') {
    TRY(ujson_consume(uj, 'r'));
    TRY(ujson_consume(uj, 'u'));
    TRY(ujson_consume(uj, 'e'));
    *value = true;
  } else if (got == 'f') {
    TRY(ujson_consume(uj, 'a'));
    TRY(ujson_consume(uj, 'l'));
    TRY(ujson_consume(uj, 's'));
    TRY(ujson_consume(uj, 'e'));
    *value = false;
  } else {
    ujson_ungetc(uj, got);
    return NOT_FOUND();
  }
  return OK_STATUS();
}

status_t ujson_deserialize_uint64_t(ujson_t *uj, uint64_t *value) {
  return ujson_parse_integer(uj, (void *)value, sizeof(*value));
}
status_t ujson_deserialize_uint32_t(ujson_t *uj, uint32_t *value) {
  return ujson_parse_integer(uj, (void *)value, sizeof(*value));
}
status_t ujson_deserialize_uint16_t(ujson_t *uj, uint16_t *value) {
  return ujson_parse_integer(uj, (void *)value, sizeof(*value));
}
status_t ujson_deserialize_uint8_t(ujson_t *uj, uint8_t *value) {
  return ujson_parse_integer(uj, (void *)value, sizeof(*value));
}
status_t ujson_deserialize_size_t(ujson_t *uj, size_t *value) {
  return ujson_parse_integer(uj, (void *)value, sizeof(*value));
}
status_t ujson_deserialize_int64_t(ujson_t *uj, int64_t *value) {
  return ujson_parse_integer(uj, (void *)value, sizeof(*value));
}
status_t ujson_deserialize_int32_t(ujson_t *uj, int32_t *value) {
  return ujson_parse_integer(uj, (void *)value, sizeof(*value));
}
status_t ujson_deserialize_int16_t(ujson_t *uj, int16_t *value) {
  return ujson_parse_integer(uj, (void *)value, sizeof(*value));
}
status_t ujson_deserialize_int8_t(ujson_t *uj, int8_t *value) {
  return ujson_parse_integer(uj, (void *)value, sizeof(*value));
}

static const char hex[] = "0123456789abcdef";

status_t ujson_serialize_string(ujson_t *uj, const char *buf) {
  uint8_t ch;
  TRY(ujson_putbuf(uj, "\"", 1));
  while ((ch = (uint8_t)*buf) != '\0') {
    if (ch < 0x20 || ch == '"' || ch == '\\' || ch >= 0x7f) {
      switch (ch) {
        case '"':
          TRY(ujson_putbuf(uj, "\\\"", 2));
          break;
        case '\\':
          TRY(ujson_putbuf(uj, "\\\\", 2));
          break;
        case '\b':
          TRY(ujson_putbuf(uj, "\\b", 2));
          break;
        case '\f':
          TRY(ujson_putbuf(uj, "\\f", 2));
          break;
        case '\n':
          TRY(ujson_putbuf(uj, "\\n", 2));
          break;
        case '\r':
          TRY(ujson_putbuf(uj, "\\r", 2));
          break;
        case '\t':
          TRY(ujson_putbuf(uj, "\\t", 2));
          break;
        default: {
          char esc[] = {'\\', 'u', '0', '0', hex[ch >> 4], hex[ch & 0xF]};
          TRY(ujson_putbuf(uj, esc, sizeof(esc)));
        }
      }
    } else {
      TRY(ujson_putbuf(uj, buf, 1));
    }
    ++buf;
  }
  TRY(ujson_putbuf(uj, "\"", 1));
  return OK_STATUS();
}

static status_t ujson_serialize_integer64(ujson_t *uj, uint64_t value,
                                          bool neg) {
  char buf[24];
  char *end = buf + sizeof(buf);
  size_t len = 0;
  *--end = '\0';

  // If negative, two's complement for the absolute value.
  if (neg)
    value = ~value + 1;
  do {
    // We've banned __udivdi3; do division with the replacement function.
    uint64_t remainder;
    value = udiv64_slow(value, 10, &remainder);
    *--end = '0' + (char)remainder;
    ++len;
  } while (value);
  if (neg) {
    *--end = '-';
    ++len;
  }
  TRY(ujson_putbuf(uj, end, len));
  return OK_STATUS();
}

static status_t ujson_serialize_integer32(ujson_t *uj, uint32_t value,
                                          bool neg) {
  char buf[24];
  char *end = buf + sizeof(buf);
  size_t len = 0;
  *--end = '\0';

  // If negative, two's complement for the absolute value.
  if (neg)
    value = ~value + 1;
  do {
    *--end = '0' + value % 10;
    value /= 10;
    ++len;
  } while (value);
  if (neg) {
    *--end = '-';
    ++len;
  }
  TRY(ujson_putbuf(uj, end, len));
  return OK_STATUS();
}

status_t ujson_serialize_bool(ujson_t *uj, const bool *value) {
  if (*value) {
    TRY(ujson_putbuf(uj, "true", 4));
  } else {
    TRY(ujson_putbuf(uj, "false", 5));
  }
  return OK_STATUS();
}

status_t ujson_serialize_uint64_t(ujson_t *uj, const uint64_t *value) {
  return ujson_serialize_integer64(uj, *value, false);
}
status_t ujson_serialize_uint32_t(ujson_t *uj, const uint32_t *value) {
  return ujson_serialize_integer32(uj, *value, false);
}

status_t ujson_serialize_uint16_t(ujson_t *uj, const uint16_t *value) {
  return ujson_serialize_integer32(uj, *value, false);
}

status_t ujson_serialize_uint8_t(ujson_t *uj, const uint8_t *value) {
  return ujson_serialize_integer32(uj, *value, false);
}

status_t ujson_serialize_size_t(ujson_t *uj, const size_t *value) {
  if (sizeof(size_t) == sizeof(uint64_t)) {
    return ujson_serialize_integer64(uj, *value, false);
  } else {
    return ujson_serialize_integer32(uj, *value, false);
  }
}

status_t ujson_serialize_int64_t(ujson_t *uj, const int64_t *value) {
  return ujson_serialize_integer64(uj, (uint64_t)*value, *value < 0);
}

status_t ujson_serialize_int32_t(ujson_t *uj, const int32_t *value) {
  return ujson_serialize_integer32(uj, (uint32_t)*value, *value < 0);
}

status_t ujson_serialize_int16_t(ujson_t *uj, const int16_t *value) {
  return ujson_serialize_integer32(uj, (uint32_t)*value, *value < 0);
}

status_t ujson_serialize_int8_t(ujson_t *uj, const int8_t *value) {
  return ujson_serialize_integer32(uj, (uint32_t)*value, *value < 0);
}

status_t ujson_deserialize_status_t(ujson_t *uj, status_t *value) {
  private_status_t code;
  uint32_t module_id = 0;
  uint32_t arg = 0;
  TRY(ujson_consume(uj, '{'));
  TRY(ujson_deserialize_private_status_t(uj, &code));
  TRY(ujson_consume(uj, ':'));
  if (TRY(ujson_consume_maybe(uj, '['))) {
    char module[4];
    TRY(ujson_parse_qs(uj, module, sizeof(module)));
    module_id = MAKE_MODULE_ID(module[0], module[1], module[2]);
    TRY(ujson_consume(uj, ','));
    TRY(ujson_deserialize_uint32_t(uj, &arg));
    TRY(ujson_consume(uj, ']'));
  } else {
    TRY(ujson_deserialize_uint32_t(uj, &arg));
  }
  TRY(ujson_consume(uj, '}'));
  *value =
      status_create((absl_status_t)code, module_id, __FILE__, (int32_t)arg);
  return OK_STATUS();
}

status_t ujson_serialize_status_t(ujson_t *uj, const status_t *value) {
  buffer_sink_t out = {
      .data = uj->io_context,
      .sink = (size_t(*)(void *, const char *, size_t))uj->putbuf,
  };
  base_fprintf(out, "%!r", *value);
  return OK_STATUS();
}
