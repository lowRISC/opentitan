// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BASE_MOCK_SEC_MMIO_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BASE_MOCK_SEC_MMIO_H_

#include "sw/device/lib/base/testing/mock_mmio_test_utils.h"
#include "sw/device/lib/testing/mask_rom_test.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"

namespace mask_rom_test {
namespace internal {
/**
 * Mock class for abs_mmio.c.
 */
class MockSecMmio {
 public:
  MOCK_METHOD(void, Init, (sec_mmio_shutdown_handler callee));
  MOCK_METHOD(uint32_t, Read32, (uint32_t addr));
  MOCK_METHOD(void, Write32, (uint32_t addr, uint32_t value));
  MOCK_METHOD(void, WriteIncrement, (uint32_t value));
  MOCK_METHOD(void, CheckValues, (uint32_t rnd_offset));
  MOCK_METHOD(void, CheckCounters, (uint32_t expected_check_count));

  virtual ~MockSecMmio() {}
};
}  // namespace internal

using MockSecMmio = GlobalMock<testing::StrictMock<internal::MockSecMmio>>;

/**
 * Expect a read to the device `dev` at the given offset, returning the given
 * 32-bit value.
 *
 * The value may be given as an integer, a pointer to little-endian data,
 * or a `std::initializer_list<BitField>`.
 *
 * This expectation is sequenced with all other `EXPECT_SEC_READ` and
 * `EXPECT_SEC_WRITE` calls.
 */
#define EXPECT_SEC_READ32(mmio, addr, ...) \
  EXPECT_CALL(mmio, Read32(addr))          \
      .WillOnce(testing::Return(mock_mmio::ToInt<uint32_t>(__VA_ARGS__)))

/**
 * Expect a write to the given offset with the given 32-bit value.
 *
 * The value may be given as an integer, a pointer to little-endian data,
 * or a `std::initializer_list<BitField>`.
 *
 * This function is only available in tests using a fixture that derives
 * `MmioTest`.
 *
 * This expectation is sequenced with all other `EXPECT_SEC_READ` and
 * `EXPECT_SEC_WRITE` calls.
 */
#define EXPECT_SEC_WRITE32(mmio, addr, ...) \
  EXPECT_CALL(mmio, Write32(addr, mock_mmio::ToInt<uint32_t>(__VA_ARGS__)));

extern "C" {

void sec_mmio_init(sec_mmio_shutdown_handler callee) {
  MockSecMmio::Instance().Init(callee);
}

uint32_t sec_mmio_read32(uint32_t addr) {
  MockSecMmio::Instance().Read32(addr);
}

void sec_mmio_write32(uint32_t addr, uint32_t value) {
  MockSecMmio::Instance().Write32(addr, value);
}

void sec_mmio_write_increment(uint32_t value) {
  MockSecMmio::Instance().WriteIncrement(value);
}

void sec_mmio_check_values(uint32_t rnd_offset) {
  MockSecMmio::Instance().CheckValues(rnd_offset);
}

void sec_mmio_check_counters(uint32_t expected_check_count) {
  MockSecMmio::Instance().CheckCounters(expected_check_count);
}

}  // extern "C"
}  // namespace mask_rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BASE_MOCK_SEC_MMIO_H_
