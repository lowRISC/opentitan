// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/crc32.h"

#include <stdbool.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"

#ifdef OT_PLATFORM_RV32
static uint32_t crc32_internal_add8(uint32_t ctx, uint8_t byte) {
  ctx ^= byte;
  asm(".option push;"
      ".option arch, +zbr0p93;"
      "crc32.b %0, %1;"
      ".option pop;"
      : "+r"(ctx));
  return ctx;
}

static uint32_t crc32_internal_add32(uint32_t ctx, uint32_t word) {
  ctx ^= word;
  asm(".option push;"
      ".option arch, +zbr0p93;"
      "crc32.w %0, %1;"
      ".option pop;"
      : "+r"(ctx));
  return ctx;
}
#else
enum {
  /**
   * CRC32 polynomial.
   */
  kCrc32Poly = 0xedb88320,
};

/**
 * Computes the CRC32 of a buffer as expected by Python's `zlib.crc32()`. The
 * implementation below is basically a simplified, i.e. byte-by-byte and without
 * a lookup table, version of zlib's crc32, which also matches IEEE 802.3
 * CRC-32. See
 * https://github.com/madler/zlib/blob/2fa463bacfff79181df1a5270fb67cc679a53e71/crc32.c,
 * lines 111-112 and 276-279.
 */
static uint32_t crc32_internal_add8(uint32_t ctx, uint8_t byte) {
  ctx ^= byte;
  for (size_t i = 0; i < 8; ++i) {
    bool lsb = ctx & 1;
    ctx >>= 1;
    if (lsb) {
      ctx ^= kCrc32Poly;
    }
  }
  return ctx;
}

static uint32_t crc32_internal_add32(uint32_t ctx, uint32_t word) {
  char *bytes = (char *)&word;
  for (size_t i = 0; i < sizeof(uint32_t); ++i) {
    ctx = crc32_internal_add8(ctx, bytes[i]);
  }
  return ctx;
}
#endif

void crc32_init(uint32_t *ctx) { *ctx = UINT32_MAX; }

void crc32_add8(uint32_t *ctx, uint8_t byte) {
  *ctx = crc32_internal_add8(*ctx, byte);
}

void crc32_add32(uint32_t *ctx, uint32_t word) {
  *ctx = crc32_internal_add32(*ctx, word);
}

void crc32_add(uint32_t *ctx, const void *buf, size_t len) {
  const char *data = buf;
  uint32_t state = *ctx;
  // Unaligned head.
  for (; len > 0 && (uintptr_t)data & 0x3; --len, ++data) {
    state = crc32_internal_add8(state, *data);
  }
  // Aligned body.
  for (; len >= sizeof(uint32_t);
       len -= sizeof(uint32_t), data += sizeof(uint32_t)) {
    state = crc32_internal_add32(state, read_32(data));
  }
  // Unaligned tail.
  for (; len > 0; --len, ++data) {
    state = crc32_internal_add8(state, *data);
  }
  *ctx = state;
}

uint32_t crc32_finish(const uint32_t *ctx) { return *ctx ^ UINT32_MAX; }

uint32_t crc32(const void *buf, size_t len) {
  uint32_t ctx;
  crc32_init(&ctx);
  crc32_add(&ctx, buf, len);
  return crc32_finish(&ctx);
}
