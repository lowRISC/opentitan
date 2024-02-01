// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/hexstr.h"

static const char hex[] = "0123456789abcdef";

status_t hexstr_encode(char *dst, size_t dst_size, const void *src,
                       size_t src_size) {
  const uint8_t *data = (const uint8_t *)src;
  for (; src_size > 0; --src_size, ++data) {
    if (dst_size < 3) {
      return INVALID_ARGUMENT();
    }
    *dst++ = hex[*data >> 4];
    *dst++ = hex[*data & 15];
    dst_size -= 2;
  }
  *dst = '\0';
  return OK_STATUS();
}

static status_t decode_nibble(char ch) {
  if (ch == 0) {
    // Unexpected end of string.
    return INVALID_ARGUMENT();
  }
  int nibble = (ch >= '0' && ch <= '9')   ? ch - '0'
               : (ch >= 'A' && ch <= 'F') ? ch - 'A' + 10
               : (ch >= 'a' && ch <= 'f') ? ch - 'a' + 10
                                          : -1;
  if (nibble == -1) {
    // Not a valid hex digit.
    return INVALID_ARGUMENT();
  }
  return OK_STATUS(nibble);
}

status_t hexstr_decode(void *dst, size_t dst_size, const char *src) {
  uint8_t *data = (uint8_t *)dst;
  while (*src) {
    if (dst_size == 0) {
      // Dest buffer too short.
      return INVALID_ARGUMENT();
    }
    // Decode two hex digits the destination byte.
    uint8_t nibble = (uint8_t)TRY(decode_nibble(*src++));
    *data = (uint8_t)(nibble << 4);
    nibble = (uint8_t)TRY(decode_nibble(*src++));
    *data |= nibble;

    ++data;
    --dst_size;
  }
  return OK_STATUS();
}
