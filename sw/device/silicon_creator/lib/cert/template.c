// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/cert/template.h"

#include <limits.h>

static const char kLowercaseHexChars[16] = {'0', '1', '2', '3', '4', '5',
                                            '6', '7', '8', '9', 'a', 'b',
                                            'c', 'd', 'e', 'f'};

uint8_t *template_push_hex_impl(uint8_t *out, const uint8_t *bytes,
                                size_t size) {
  while (size > 0) {
    *out++ = (uint8_t)kLowercaseHexChars[bytes[0] >> 4];
    *out++ = (uint8_t)kLowercaseHexChars[bytes[0] & 0xf];
    bytes++;
    size--;
  }
  return out;
}

uint8_t *template_asn1_integer_impl(uint8_t *out, uint8_t tag, bool tweak_msb,
                                    const uint8_t *bytes_be, size_t size) {
  *out++ = tag;
  uint8_t *size_ptr = out++;
  if (tweak_msb) {
    *out++ = 0;  // additional zero prefix;
  } else {
    while (size > 0 && *bytes_be == 0) {
      ++bytes_be;
      --size;
    }
    if (size == 0 || *bytes_be > 0x7f) {
      *out++ = 0;
    }
  }
  memcpy(out, bytes_be, size);
  if (tweak_msb)
    out[0] |= 0x80;
  out += size;
  *size_ptr = (uint8_t)(out - size_ptr) - 1;
  return out;
}

void template_patch_size_be_impl(template_pos_t memo, uint8_t *out_end) {
  *(uint16_t *)memo = __builtin_bswap16(__builtin_bswap16(*(uint16_t *)memo) +
                                        (uint16_t)(out_end - (uint8_t *)memo));
}

uint8_t *template_patch_size_der_impl(template_pos_t memo, uint8_t *out_end) {
  uint8_t *memo_ptr = (uint8_t *)memo;
  const size_t kReservedLen = 3;

  size_t content_size = (size_t)(out_end - (memo_ptr + kReservedLen));

  size_t der_len_bytes = 0;
  if (content_size <= 0x7f) {
    memo_ptr[0] = (uint8_t)content_size;
    der_len_bytes = 1;
  } else if (content_size <= 0xff) {
    memo_ptr[0] = 0x81;
    memo_ptr[1] = (uint8_t)content_size;
    der_len_bytes = 2;
  } else {
    memo_ptr[0] = 0x82;
    memo_ptr[1] = (uint8_t)(content_size >> 8);
    memo_ptr[2] = (uint8_t)(content_size & 0xff);
    der_len_bytes = 3;
  }

  if (der_len_bytes < kReservedLen) {
    uint8_t *src = memo_ptr + kReservedLen;
    uint8_t *dst = memo_ptr + der_len_bytes;
    while (src < out_end) {
      *dst++ = *src++;
    }
    out_end = dst;
  }

  return out_end;
}
