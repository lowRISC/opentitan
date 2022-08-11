// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/crc32.h"

#include <stdbool.h>

#include "sw/device/lib/base/memory.h"

enum {
  /**
   * CRC32 polynomial.
   */
  kCrc32Poly = 0xedb88320,
};

void crc32_init(uint32_t *ctx) { *ctx = UINT32_MAX; }

/**
 * Computes the CRC32 of a buffer as expected by Python's `zlib.crc32()`. The
 * implementation below is basically a simplified, i.e. byte-by-byte and without
 * a lookup table, version of zlib's crc32, which also matches IEEE 802.3
 * CRC-32. See
 * https://github.com/madler/zlib/blob/2fa463bacfff79181df1a5270fb67cc679a53e71/crc32.c,
 * lines 111-112 and 276-279.
 */
void crc32_add8(uint32_t *ctx, uint8_t byte) {
  *ctx ^= byte;
  for (size_t i = 0; i < 8; ++i) {
    bool lsb = *ctx & 1;
    *ctx >>= 1;
    if (lsb) {
      *ctx ^= kCrc32Poly;
    }
  }
}

void crc32_add32(uint32_t *ctx, uint32_t word) {
  char *bytes = (char *)&word;
  for (size_t i = 0; i < sizeof(uint32_t); ++i) {
    crc32_add8(ctx, bytes[i]);
  }
}

void crc32_add(uint32_t *ctx, const void *buf, size_t len) {
  const char *data = buf;

  // Unaligned head.
  for (; len > 0 && (uintptr_t)data & 0x3; --len, ++data) {
    crc32_add8(ctx, *data);
  }
  // Aligned body.
  for (; len >= sizeof(uint32_t);
       len -= sizeof(uint32_t), data += sizeof(uint32_t)) {
    crc32_add32(ctx, read_32(data));
  }
  // Unaligned tail.
  for (; len > 0; --len, ++data) {
    crc32_add8(ctx, *data);
  }
}

uint32_t crc32_finish(const uint32_t *ctx) { return *ctx ^ UINT32_MAX; }

uint32_t crc32(const void *buf, size_t len) {
  uint32_t ctx;
  crc32_init(&ctx);
  crc32_add(&ctx, buf, len);
  return crc32_finish(&ctx);
}
