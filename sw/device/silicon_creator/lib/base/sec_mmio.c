// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/base/sec_mmio.h"

#include <assert.h>

#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/base/abs_mmio.h"

// The context is declared as weak so that the mask ROM and ROM_EXT may
// override its location.
__attribute__((weak)) volatile sec_mmio_ctx_t sec_mmio_ctx;

// FIXME: Replace for shutdown module handler.
static sec_mmio_shutdown_handler sec_mmio_shutdown_cb;

enum {
  // Value with good hamming weight used to mask the stored expected value.
  kSecMmioMaskVal = 0x21692436u,

  // This must be set to a prime number greater than the number of items in
  // `sec_mmio_ctx.addrs`. Used to generate random read order permutations.
  kSecMmioRndStep = 211u,
};

static_assert((uint32_t)kSecMmioRndStep > (uint32_t)kSecMmioRegFileSize,
              "kSecMmioRndStep not large enough");

/**
 * Updates or inserts the register entry pointed to by MMIO `addr` with the
 * given `value`.
 *
 * Increments the `sec_mmio_ctx.last_index`.
 */
static void upsert_register(uint32_t addr, uint32_t value) {
  size_t i = 0;
  for (; i < sec_mmio_ctx.last_index; ++i) {
    if (sec_mmio_ctx.addrs[i] == addr) {
      sec_mmio_ctx.values[i] = value;
      break;
    }
  }
  if (i == sec_mmio_ctx.last_index && i < kSecMmioRegFileSize) {
    sec_mmio_ctx.addrs[i] = addr;
    sec_mmio_ctx.values[i] = value;
    ++sec_mmio_ctx.last_index;
  }
  // The following condition check serves as an additional fault detection
  // mechanism.
  if (i >= kSecMmioRegFileSize) {
    sec_mmio_shutdown_cb(kErrorSecMmioRegFileSize);
    __builtin_unreachable();
  }
}

void sec_mmio_init(sec_mmio_shutdown_handler cb) {
  sec_mmio_shutdown_cb = cb;
  sec_mmio_ctx.last_index = 0;
  sec_mmio_ctx.write_count = 0;
  sec_mmio_ctx.check_count = 0;
  sec_mmio_ctx.expected_write_count = 0;
  for (size_t i = 0; i < ARRAYSIZE(sec_mmio_ctx.addrs); ++i) {
    sec_mmio_ctx.addrs[i] = UINT32_MAX;
  }
}

uint32_t sec_mmio_read32(uint32_t addr) {
  uint32_t value = abs_mmio_read32(addr);
  uint32_t masked_value = value ^ kSecMmioMaskVal;

  upsert_register(addr, value);

  if ((abs_mmio_read32(addr) ^ kSecMmioMaskVal) != masked_value) {
    sec_mmio_shutdown_cb(kErrorSecMmioReadFault);
    __builtin_unreachable();
  }
  return value;
}

void sec_mmio_write32(uint32_t addr, uint32_t value) {
  abs_mmio_write32(addr, value);
  uint32_t masked_value = value ^ kSecMmioMaskVal;

  upsert_register(addr, masked_value);

  if ((abs_mmio_read32(addr) ^ kSecMmioMaskVal) != masked_value) {
    sec_mmio_shutdown_cb(kErrorSecMmioWriteFault);
    __builtin_unreachable();
  }
  ++sec_mmio_ctx.write_count;
}

void sec_mmio_write32_shadowed(uint32_t addr, uint32_t value) {
  // Shadowed registers require two writes.
  abs_mmio_write32(addr, value);
  abs_mmio_write32(addr, value);
  uint32_t masked_value = value ^ kSecMmioMaskVal;

  upsert_register(addr, masked_value);

  if ((abs_mmio_read32(addr) ^ kSecMmioMaskVal) != masked_value) {
    sec_mmio_shutdown_cb(kErrorSecMmioWriteFault);
    __builtin_unreachable();
  }
  ++sec_mmio_ctx.write_count;
}

void sec_mmio_write_increment(uint32_t value) {
  sec_mmio_ctx.expected_write_count += value;
}

void sec_mmio_check_values(uint32_t rnd_offset) {
  size_t offset = rnd_offset;
  size_t i;
  for (i = 0; i < sec_mmio_ctx.last_index; ++i) {
    // FIXME: Remove dependency on __udivdi3.
    offset = (offset + kSecMmioRndStep) % sec_mmio_ctx.last_index;
    uint32_t read_value = abs_mmio_read32(sec_mmio_ctx.addrs[offset]);
    if ((read_value ^ kSecMmioMaskVal) != sec_mmio_ctx.values[offset]) {
      sec_mmio_shutdown_cb(kErrorSecMmioCheckValueFault);
      __builtin_unreachable();
    }
  }
  // Check for loop completion.
  if (i != sec_mmio_ctx.last_index) {
    sec_mmio_shutdown_cb(kErrorSecMmioCheckIndexFault);
    __builtin_unreachable();
  }
  ++sec_mmio_ctx.check_count;
}

void sec_mmio_check_counters(uint32_t expected_check_count) {
  // Generous use of volatile in critical variables to avoid compiler
  // optimizations, and map "zero" to a value with good hamming weight
  // and with a good hamming distance to "all-ones".
  // TODO(#6610): Update based on implementation guidance.
  static volatile const uint32_t kValZero = 0x3ca5965a;
  static volatile const uint32_t kValOnes = 0xc35a69a5;

  uint32_t result = kValZero ^ sec_mmio_ctx.write_count;
  result ^= sec_mmio_ctx.expected_write_count;

  // Check the expected write count. This is equivalent to
  // sec_mmio_ctx.write_count == sec_mmio_ctx.expected_write_count
  if (result != kValZero) {
    sec_mmio_shutdown_cb(kErrorSecMmioWriteCountFault);
    __builtin_unreachable();
  }

  // Check the expected check counts. This is equivalent to
  // sec_mmio_ctx.check_count == expected_check_count. This check is expected to
  // fail if the previous check failed.
  result ^= sec_mmio_ctx.check_count;
  result ^= expected_check_count;
  if (~result != kValOnes) {
    sec_mmio_shutdown_cb(kErrorSecMmioCheckCountFault);
    __builtin_unreachable();
  }
  ++sec_mmio_ctx.check_count;
}
