// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/crc32.h"

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"

void crc32_init(uint32_t *ctx) { *ctx = UINT32_MAX; }

void crc32_add8(uint32_t *ctx, uint8_t byte) {
#ifdef OT_PLATFORM_RV32
  *ctx ^= byte;
  asm("crc32.b %0, %1;" : "+r"(*ctx));
#else
  static_assert(false, "crc32_add8 does not have a pure C implementation.");
#endif
}

void crc32_add32(uint32_t *ctx, uint32_t word) {
#ifdef OT_PLATFORM_RV32
  *ctx ^= word;
  asm("crc32.w %0, %1;" : "+r"(*ctx));
#else
  static_assert(false, "crc32_add32 does not have a pure C implementation.");
#endif
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
