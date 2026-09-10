// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/lz4.h"

#include <stdint.h>

int LZ4_decompress(const char *src_in, char *dst_in, int compressed_size,
                   int dst_capacity) {
  const uint8_t *src = (const uint8_t *)src_in;
  const uint8_t *src_end = src + compressed_size;
  uint8_t *dst = (uint8_t *)dst_in;
  uint8_t *dst_end = dst + dst_capacity;
  uint8_t *dst_ptr = dst;

  while (src < src_end) {
    uint8_t token = *src++;

    // Process literals
    unsigned int lit_len = token >> 4;
    if (lit_len == 15) {
      uint8_t s;
      do {
        if (src >= src_end)
          return -1;  // Unexpected end of src
        s = *src++;
        lit_len += s;
      } while (s == 255);
    }

    if (lit_len > 0) {
      if ((size_t)(src_end - src) < lit_len ||
          (size_t)(dst_end - dst_ptr) < lit_len) {
        return -1;
      }

      unsigned int l = lit_len;
      do {
        *dst_ptr++ = *src++;
      } while (--l);
    }

    if (src >= src_end) {
      break;
    }

    // Process match offset
    if (src + 2 > src_end)
      return -1;
    uint16_t offset = (uint16_t)(src[0] | (src[1] << 8));
    src += 2;

    if (offset == 0 || offset > (size_t)(dst_ptr - dst)) {
      return -1;  // Offset out of bounds
    }

    unsigned int match_len = token & 0x0F;
    if (match_len == 15) {
      uint8_t s;
      do {
        if (src >= src_end)
          return -1;
        s = *src++;
        match_len += s;
      } while (s == 255);
    }
    match_len += 4;

    // Check bounds for match destination
    if ((size_t)(dst_end - dst_ptr) < match_len) {
      return -1;
    }

    const uint8_t *match_ptr = dst_ptr - offset;
    unsigned int m = match_len;
    do {
      *dst_ptr++ = *match_ptr++;
    } while (--m);
  }

  return (int)(dst_ptr - dst);
}
