// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/base/sec_mmio.h"

#include <array>
#include <cstdlib>
#include <vector>

#include "gtest/gtest.h"
#include "sw/device/lib/base/mock_abs_mmio.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace sec_mmio_unittest {
namespace {
using ::testing::Each;
using ::testing::ElementsAreArray;
using ::testing::Eq;

class SecMmioTest : public rom_test::RomTest {
 protected:
  void SetUp() override { sec_mmio_init(); }
  sec_mmio_ctx_t *ctx_ = &::sec_mmio_ctx;
  rom_test::MockAbsMmio mmio_;
};

TEST_F(SecMmioTest, Initialize) {
  // Write non-zero values to critical fields before calling `sec_mmio_init()`.
  ctx_->check_count = 1;
  ctx_->expected_write_count = 1;
  ctx_->last_index = 1;
  ctx_->write_count = 1;
  ctx_->addrs[0] = 0;
  sec_mmio_init();

  EXPECT_EQ(ctx_->check_count, 0);
  EXPECT_EQ(ctx_->expected_write_count, 0);
  EXPECT_EQ(ctx_->last_index, 0);
  EXPECT_EQ(ctx_->write_count, 0);
  EXPECT_THAT(ctx_->addrs, Each(Eq(UINT32_MAX)));
  EXPECT_THAT(ctx_->values, Each(Eq(UINT32_MAX)));
}

TEST_F(SecMmioTest, NextStageInitialize) {
  // Ensure the register file size is greater than zero to ensure checks are
  // performed on non-zero sized arrays.
  static_assert(kSecMmioRegFileSize > 2,
                "kSecMmioRegFileSize must be greater than 2");
  std::array<uint32_t, kSecMmioRegFileSize> expected_addrs;
  std::array<uint32_t, kSecMmioRegFileSize> expected_values;

  // Prefill data to simulate a pre-initialization conditions. Use different
  // values for `addr` and `values` to ensure the test checks are specific for
  // each array.
  for (size_t i = 0; i < kSecMmioRegFileSize; ++i) {
    ctx_->addrs[i] = i ^ 0xa;
    ctx_->values[i] = i ^ 0x5;
    expected_addrs[i] = ctx_->addrs[i];
    expected_values[i] = ctx_->values[i];
  }

  ctx_->check_count = 5;
  ctx_->expected_write_count = 6;
  ctx_->write_count = 6;

  const uint32_t kExpectedWriteCount = kSecMmioRegFileSize / 2;
  ctx_->last_index = kExpectedWriteCount;

  for (size_t i = kExpectedWriteCount; i < kSecMmioRegFileSize; ++i) {
    expected_addrs[i] = UINT32_MAX;
    expected_values[i] = UINT32_MAX;
  }

  sec_mmio_next_stage_init();

  EXPECT_EQ(ctx_->write_count, 6);
  EXPECT_EQ(ctx_->expected_write_count, 6);
  EXPECT_EQ(ctx_->last_index, kExpectedWriteCount);
  EXPECT_EQ(ctx_->check_count, 0);
  EXPECT_THAT(ctx_->addrs, ElementsAreArray(expected_addrs));
  EXPECT_THAT(ctx_->values, ElementsAreArray(expected_values));
}

TEST_F(SecMmioTest, Read32OrDie) {
  EXPECT_ABS_READ32(0, 0x12345678);
  EXPECT_ABS_READ32(0, 0x12345678);
  EXPECT_EQ(sec_mmio_read32(0), 0x12345678);

  EXPECT_ABS_READ32(4, 0x87654321);
  EXPECT_ABS_READ32(4, 0x87654321);
  EXPECT_EQ(sec_mmio_read32(4), 0x87654321);

  EXPECT_ABS_READ32(0, 0x87654321);
  EXPECT_ABS_READ32(0, 0x87654321);
  EXPECT_EQ(sec_mmio_read32(0), 0x87654321);

  // Two of the operations were targeting the same offset, so we only expect two
  // operations and zero shutdown attempts.
  EXPECT_EQ(ctx_->write_count, 0);
  EXPECT_EQ(ctx_->last_index, 2);
}

TEST_F(SecMmioTest, Write32) {
  EXPECT_ABS_WRITE32(0, 0x12345678);
  EXPECT_ABS_READ32(0, 0x12345678);
  sec_mmio_write32(0, 0x12345678);
  EXPECT_EQ(ctx_->write_count, 1);

  EXPECT_ABS_WRITE32(4, 0x87654321);
  EXPECT_ABS_READ32(4, 0x87654321);
  sec_mmio_write32(4, 0x87654321);
  EXPECT_EQ(ctx_->write_count, 2);

  EXPECT_ABS_WRITE32(0, 0x87654321);
  EXPECT_ABS_READ32(0, 0x87654321);
  sec_mmio_write32(0, 0x87654321);
  EXPECT_EQ(ctx_->write_count, 3);

  // Two of the operations were targeting the same offset, so we only expect two
  // operations.
  EXPECT_EQ(ctx_->last_index, 2);
}

TEST_F(SecMmioTest, CheckValues) {
  EXPECT_ABS_WRITE32(0, 0x12345678);
  EXPECT_ABS_READ32(0, 0x12345678);
  sec_mmio_write32(0, 0x12345678);

  EXPECT_ABS_WRITE32(4, 0x87654321);
  EXPECT_ABS_READ32(4, 0x87654321);
  sec_mmio_write32(4, 0x87654321);

  EXPECT_ABS_WRITE32(8, 0);
  EXPECT_ABS_READ32(8, 0);
  sec_mmio_write32(8, 0);

  // Test an expected value modification which gets updated by a read.
  EXPECT_ABS_READ32(8, 0xa5a5a5a5);
  EXPECT_ABS_READ32(8, 0xa5a5a5a5);
  EXPECT_EQ(sec_mmio_read32(8), 0xa5a5a5a5);

  // The expected permutation order for rnd_offset=0
  EXPECT_ABS_READ32(0, 0x12345678);
  EXPECT_ABS_READ32(4, 0x87654321);
  EXPECT_ABS_READ32(8, 0xa5a5a5a5);
  sec_mmio_check_values(/*rnd_offset=*/0);
  EXPECT_EQ(ctx_->check_count, 1);

  // The expected permutation order for rnd_offset=0x80000000
  EXPECT_ABS_READ32(4, 0x87654321);
  EXPECT_ABS_READ32(8, 0xa5a5a5a5);
  EXPECT_ABS_READ32(0, 0x12345678);
  sec_mmio_check_values(/*rnd_offset=*/0x80000000);
  EXPECT_EQ(ctx_->check_count, 2);

  // The expected permutation order for rnd_offset=0xf0000000
  EXPECT_ABS_READ32(8, 0xa5a5a5a5);
  EXPECT_ABS_READ32(0, 0x12345678);
  EXPECT_ABS_READ32(4, 0x87654321);
  sec_mmio_check_values(/*rnd_offset=*/0xf0000000);
  EXPECT_EQ(ctx_->check_count, 3);
}

TEST_F(SecMmioTest, CheckCount) {
  EXPECT_ABS_WRITE32(0, 0x12345678);
  EXPECT_ABS_READ32(0, 0x12345678);
  sec_mmio_write32(0, 0x12345678);
  SEC_MMIO_WRITE_INCREMENT(1);

  sec_mmio_check_counters(/*expected_check_count=*/0);
  sec_mmio_check_counters(/*expected_check_count=*/1);
  EXPECT_EQ(ctx_->check_count, 2);
}

// Negative test cases trigger assertions, which are caugth by `EXPECT_DEATH`
// calls.
class SecMmioDeathTest : public SecMmioTest {};

TEST_F(SecMmioDeathTest, Read32OrDieSimulatedFault) {
  EXPECT_DEATH(
      {
        EXPECT_ABS_READ32(0, 0x12345678);
        EXPECT_ABS_READ32(0, 0);
        sec_mmio_read32(0);
      },
      "");
}

TEST_F(SecMmioDeathTest, Write32SimulatedFault) {
  EXPECT_DEATH(
      {
        EXPECT_ABS_WRITE32(0, 0x12345678);
        EXPECT_ABS_READ32(0, 0);
        sec_mmio_write32(0, 0x12345678);
      },
      "");
}

TEST_F(SecMmioDeathTest, CheckValuesSimulatedFault) {
  EXPECT_DEATH(
      {
        EXPECT_ABS_WRITE32(0, 0x12345678);
        EXPECT_ABS_READ32(0, 0x12345678);
        sec_mmio_write32(0, 0x12345678);

        EXPECT_ABS_READ32(0, 0);
        sec_mmio_check_values(/*rnd_offset=*/0);
      },
      "");
}

TEST_F(SecMmioDeathTest, CheckCountWriteMismatch) {
  // The developer forgot to increment the write counter, or an attacker
  // glitched the sec write operation.
  EXPECT_DEATH(
      {
        EXPECT_ABS_WRITE32(0, 0x12345678);
        EXPECT_ABS_READ32(0, 0x12345678);
        sec_mmio_write32(0, 0x12345678);
        sec_mmio_check_counters(/*expected_check_count=*/0);
      },
      "");
}

}  // namespace
}  // namespace sec_mmio_unittest
