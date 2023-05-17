// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/base/sec_mmio.h"

#include <assert.h>

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"

// The context is declared as weak so that the ROM and ROM_EXT may
// override its location.
OT_WEAK sec_mmio_ctx_t sec_mmio_ctx;

enum {
  // Value with good hamming weight used to mask the stored expected value.
  kSecMmioMaskVal = 0x21692436u,

  // Constants used for hardened comparisons. kSecMmioValZero ==
  // ~kSecMmioValOne.
  kSecMmioValZero = 0x3ca5965a,
  kSecMmioValOne = 0xc35a69a5,

  // Number of address-value pairs in the table.
  kEntryCount = ARRAYSIZE(sec_mmio_ctx.addrs),
};

/**
 * Updates or inserts the register entry pointed to by MMIO `addr` with the
 * given `value`.
 *
 * Increments the `sec_mmio_ctx.last_index`.
 */
static void upsert_register(uint32_t addr, uint32_t value) {
  const size_t last_index = sec_mmio_ctx.last_index;
  size_t i = 0, j = last_index - 1;
  for (; launder32(i) < last_index && launder32(j) < last_index; ++i, --j) {
    if (launder32(sec_mmio_ctx.addrs[i]) == addr) {
      sec_mmio_ctx.values[i] = value;
      break;
    }
  }
  if (launder32(i) == last_index && launder32(i) < kSecMmioRegFileSize) {
    HARDENED_CHECK_EQ((uint32_t)j, UINT32_MAX);
    sec_mmio_ctx.addrs[i] = addr;
    sec_mmio_ctx.values[i] = value;
    ++sec_mmio_ctx.last_index;
  }
  // The following checks serve as an additional fault detection mechanism.
  HARDENED_CHECK_EQ(sec_mmio_ctx.addrs[i], addr);
  HARDENED_CHECK_LT(i, kSecMmioRegFileSize);
}

void sec_mmio_init(void) {
  sec_mmio_ctx.last_index = launder32(0);
  sec_mmio_ctx.write_count = launder32(0);
  sec_mmio_ctx.check_count = launder32(0);
  sec_mmio_ctx.expected_write_count = launder32(0);
  size_t i = 0, r = kEntryCount - 1;
  for (; launder32(i) < kEntryCount && launder32(r) < kEntryCount; ++i, --r) {
    sec_mmio_ctx.addrs[i] = UINT32_MAX;
    sec_mmio_ctx.values[i] = UINT32_MAX;
  }
  HARDENED_CHECK_EQ(i, kEntryCount);
  HARDENED_CHECK_EQ((uint32_t)r, UINT32_MAX);
  uint32_t check = kSecMmioValZero ^ sec_mmio_ctx.last_index;
  check ^= sec_mmio_ctx.write_count;
  check ^= sec_mmio_ctx.check_count;
  check ^= sec_mmio_ctx.expected_write_count;
  HARDENED_CHECK_EQ(check, kSecMmioValZero);
}

void sec_mmio_next_stage_init(void) {
  sec_mmio_ctx.check_count = launder32(0);
  size_t i = sec_mmio_ctx.last_index,
         r = kEntryCount - sec_mmio_ctx.last_index - 1;
  for (; launder32(i) < kEntryCount && launder32(r) < kEntryCount; ++i, --r) {
    sec_mmio_ctx.addrs[i] = UINT32_MAX;
    sec_mmio_ctx.values[i] = UINT32_MAX;
  }
  HARDENED_CHECK_EQ(i, kEntryCount);
  HARDENED_CHECK_EQ((uint32_t)r, UINT32_MAX);
  HARDENED_CHECK_EQ(sec_mmio_ctx.check_count, 0);
}

uint32_t sec_mmio_read32(uint32_t addr) {
  uint32_t value = abs_mmio_read32(addr);
  uint32_t masked_value = value ^ kSecMmioMaskVal;
  barrier32(masked_value);
  upsert_register(addr, masked_value);
  HARDENED_CHECK_EQ((abs_mmio_read32(addr) ^ kSecMmioMaskVal), masked_value);

  return value;
}

void sec_mmio_write32(uint32_t addr, uint32_t value) {
  abs_mmio_write32(addr, value);
  uint32_t masked_value = value ^ kSecMmioMaskVal;
  barrier32(masked_value);
  upsert_register(addr, masked_value);
  HARDENED_CHECK_EQ((abs_mmio_read32(addr) ^ kSecMmioMaskVal), masked_value);

  ++sec_mmio_ctx.write_count;
}

void sec_mmio_write32_shadowed(uint32_t addr, uint32_t value) {
  // Shadowed registers require two writes.
  abs_mmio_write32(addr, value);
  abs_mmio_write32(addr, value);
  uint32_t masked_value = value ^ kSecMmioMaskVal;
  barrier32(masked_value);
  upsert_register(addr, masked_value);
  HARDENED_CHECK_EQ((abs_mmio_read32(addr) ^ kSecMmioMaskVal), masked_value);

  ++sec_mmio_ctx.write_count;
}

void sec_mmio_check_values(uint32_t rnd_offset) {
  const uint32_t last_index = sec_mmio_ctx.last_index;
  // Pick a random starting offset.
  uint32_t offset = ((uint64_t)rnd_offset * (uint64_t)last_index) >> 32;
  enum { kStep = 1 };
  size_t i = 0, r = last_index - 1;
  for (; launder32(i) < last_index && launder32(r) < last_index; ++i, --r) {
    uint32_t read_value = abs_mmio_read32(sec_mmio_ctx.addrs[offset]);
    HARDENED_CHECK_EQ(read_value ^ kSecMmioMaskVal,
                      sec_mmio_ctx.values[offset]);
    offset += kStep;
    if (offset >= last_index) {
      offset -= last_index;
    }
  }
  // Check for loop completion.
  HARDENED_CHECK_EQ(i, last_index);
  HARDENED_CHECK_EQ((uint32_t)r, UINT32_MAX);
  ++sec_mmio_ctx.check_count;
}

void sec_mmio_check_counters(uint32_t expected_check_count) {
  uint32_t result = launder32(kSecMmioValZero) ^ sec_mmio_ctx.write_count;
  result ^= sec_mmio_ctx.expected_write_count;

  // Check the expected write count. This is equivalent to
  // sec_mmio_ctx.write_count == sec_mmio_ctx.expected_write_count
  HARDENED_CHECK_EQ(result, kSecMmioValZero);

  // Check the expected check counts. This is equivalent to
  // sec_mmio_ctx.check_count == expected_check_count. This check is expected to
  // fail if the previous check failed.
  result ^= sec_mmio_ctx.check_count;
  result ^= expected_check_count;
  HARDENED_CHECK_EQ(~launder32(result), kSecMmioValOne);

  ++sec_mmio_ctx.check_count;
}
