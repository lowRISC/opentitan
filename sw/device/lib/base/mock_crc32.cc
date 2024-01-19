// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/mock_crc32.h"

namespace rom_test {
extern "C" {

void crc32_init(uint32_t *ctx) { MockCrc32::Instance().Init(ctx); }

void crc32_add8(uint32_t *ctx, uint8_t byte) {
  MockCrc32::Instance().Add8(ctx, byte);
}

void crc32_add32(uint32_t *ctx, uint32_t word) {
  MockCrc32::Instance().Add32(ctx, word);
}

void crc32_add(uint32_t *ctx, const void *buf, size_t len) {
  MockCrc32::Instance().Add(ctx, buf, len);
}

uint32_t crc32_finish(const uint32_t *ctx) {
  return MockCrc32::Instance().Finish(ctx);
}

uint32_t crc32(const void *buf, size_t len) {
  return MockCrc32::Instance().Crc32(buf, len);
}

}  // extern "C"
}  // namespace rom_test
