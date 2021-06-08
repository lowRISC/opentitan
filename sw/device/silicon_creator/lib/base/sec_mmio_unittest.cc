// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/base/sec_mmio.h"

#include <array>
#include <cstdlib>
#include <vector>

#include "gtest/gtest.h"
#include "sw/device/silicon_creator/lib/base/mock_abs_mmio.h"

extern "C" {
// This is an extern in the sec_mmio module.
sec_mmio_ctx_t sec_mmio_ctx;
}

namespace sec_mmio_unittest {
namespace {
using ::testing::Each;
using ::testing::Eq;
using ::testing::Test;

class SecMmioTest : public mask_rom_test::MaskRomTest {
 protected:
  void SetUp() override {
    sec_mmio_init(+[] { std::abort(); });
  }
  sec_mmio_ctx_t *ctx_ = &::sec_mmio_ctx;
  mask_rom_test::MockAbsMmio mmio_;
};

TEST_F(SecMmioTest, Initialize) {
  // Write non-zero values to critical fields before calling `sec_mmio_init()`.
  ctx_->check_count = 1;
  ctx_->expected_write_count = 1;
  ctx_->last_index = 1;
  ctx_->write_count = 1;
  ctx_->addrs[0] = 0;
  sec_mmio_init(+[] { std::abort(); });

  EXPECT_EQ(ctx_->check_count, 0);
  EXPECT_EQ(ctx_->expected_write_count, 0);
  EXPECT_EQ(ctx_->last_index, 0);
  EXPECT_EQ(ctx_->write_count, 0);
  EXPECT_THAT(ctx_->addrs, Each(Eq(UINT32_MAX)));
}

TEST_F(SecMmioTest, Read32OrDie) {
  EXPECT_ABS_READ32(mmio_, 0, 0x12345678);
  EXPECT_ABS_READ32(mmio_, 0, 0x12345678);
  EXPECT_EQ(sec_mmio_read32(0), 0x12345678);

  EXPECT_ABS_READ32(mmio_, 4, 0x87654321);
  EXPECT_ABS_READ32(mmio_, 4, 0x87654321);
  EXPECT_EQ(sec_mmio_read32(4), 0x87654321);

  EXPECT_ABS_READ32(mmio_, 0, 0x87654321);
  EXPECT_ABS_READ32(mmio_, 0, 0x87654321);
  EXPECT_EQ(sec_mmio_read32(0), 0x87654321);

  // Two of the operations were targeting the same offset, so we only expect two
  // operations and zero shutdown attempts.
  EXPECT_EQ(ctx_->write_count, 0);
  EXPECT_EQ(ctx_->last_index, 2);
}

TEST_F(SecMmioTest, Write32) {
  EXPECT_ABS_WRITE32(mmio_, 0, 0x12345678);
  EXPECT_ABS_READ32(mmio_, 0, 0x12345678);
  sec_mmio_write32(0, 0x12345678);
  EXPECT_EQ(ctx_->write_count, 1);

  EXPECT_ABS_WRITE32(mmio_, 4, 0x87654321);
  EXPECT_ABS_READ32(mmio_, 4, 0x87654321);
  sec_mmio_write32(4, 0x87654321);
  EXPECT_EQ(ctx_->write_count, 2);

  EXPECT_ABS_WRITE32(mmio_, 0, 0x87654321);
  EXPECT_ABS_READ32(mmio_, 0, 0x87654321);
  sec_mmio_write32(0, 0x87654321);
  EXPECT_EQ(ctx_->write_count, 3);

  // Two of the operations were targeting the same offset, so we only expect two
  // operations.
  EXPECT_EQ(ctx_->last_index, 2);
}

TEST_F(SecMmioTest, CounterInc) {
  sec_mmio_write_increment(5);
  EXPECT_EQ(ctx_->expected_write_count, 5);

  sec_mmio_write_increment(10);
  EXPECT_EQ(ctx_->expected_write_count, 15);
}

TEST_F(SecMmioTest, CheckValues) {
  EXPECT_ABS_WRITE32(mmio_, 0, 0x12345678);
  EXPECT_ABS_READ32(mmio_, 0, 0x12345678);
  sec_mmio_write32(0, 0x12345678);

  EXPECT_ABS_WRITE32(mmio_, 4, 0x87654321);
  EXPECT_ABS_READ32(mmio_, 4, 0x87654321);
  sec_mmio_write32(4, 0x87654321);

  EXPECT_ABS_WRITE32(mmio_, 8, 0);
  EXPECT_ABS_READ32(mmio_, 8, 0);
  sec_mmio_write32(8, 0);

  // The expected permutation order for rnd_offset=0 is {1, 2, 0}.
  EXPECT_ABS_READ32(mmio_, 4, 0x87654321);
  EXPECT_ABS_READ32(mmio_, 8, 0);
  EXPECT_ABS_READ32(mmio_, 0, 0x12345678);
  sec_mmio_check_values(/*rnd_offset=*/0);
  EXPECT_EQ(ctx_->check_count, 1);

  // The expected permutation order for rnd_offset=1 is {2, 0, 1}.
  EXPECT_ABS_READ32(mmio_, 8, 0);
  EXPECT_ABS_READ32(mmio_, 0, 0x12345678);
  EXPECT_ABS_READ32(mmio_, 4, 0x87654321);
  sec_mmio_check_values(/*rnd_offset=*/1);
  EXPECT_EQ(ctx_->check_count, 2);

  // The expected permutation order for rnd_offset=32 is {0, 1, 2}.
  EXPECT_ABS_READ32(mmio_, 0, 0x12345678);
  EXPECT_ABS_READ32(mmio_, 4, 0x87654321);
  EXPECT_ABS_READ32(mmio_, 8, 0);
  sec_mmio_check_values(/*rnd_offset=*/32);
  EXPECT_EQ(ctx_->check_count, 3);
}

TEST_F(SecMmioTest, CheckCount) {
  EXPECT_ABS_WRITE32(mmio_, 0, 0x12345678);
  EXPECT_ABS_READ32(mmio_, 0, 0x12345678);
  sec_mmio_write32(0, 0x12345678);
  sec_mmio_write_increment(1);

  sec_mmio_check_counters(/*expected_check_count=*/0);
  sec_mmio_check_counters(/*expected_check_count=*/1);
  EXPECT_EQ(ctx_->check_count, 2);
}

// Negative test cases trigger assertions, which are caugth by `ASSERT_DEATH`
// calls. All test cases use lambda functions to wrap expectations and work
// around issue google/googletest#1004.
class SecMmioDeathTest : public SecMmioTest {};

TEST_F(SecMmioDeathTest, Read32OrDieSimulatedFault) {
  auto deadly_ops = [this] {
    EXPECT_ABS_READ32(mmio_, 0, 0x12345678);
    EXPECT_ABS_READ32(mmio_, 0, 0);
    sec_mmio_read32(0);
  };
  ASSERT_DEATH(deadly_ops(), "");
}

TEST_F(SecMmioDeathTest, Write32SimulatedFault) {
  auto deadly_ops = [this] {
    EXPECT_ABS_WRITE32(mmio_, 0, 0x12345678);
    EXPECT_ABS_READ32(mmio_, 0, 0);
    sec_mmio_write32(0, 0x12345678);
  };
  ASSERT_DEATH(deadly_ops(), "");
}

TEST_F(SecMmioDeathTest, CheckValuesSimulatedFault) {
  auto deadly_ops = [this] {
    EXPECT_ABS_WRITE32(mmio_, 0, 0x12345678);
    EXPECT_ABS_READ32(mmio_, 0, 0x12345678);
    sec_mmio_write32(0, 0x12345678);

    EXPECT_ABS_READ32(mmio_, 0, 0);
    sec_mmio_check_values(/*rnd_offset=*/0);
  };
  ASSERT_DEATH(deadly_ops(), "");
}

TEST_F(SecMmioDeathTest, CheckCountWriteMismatch) {
  auto deadly_ops = [this] {
    EXPECT_ABS_WRITE32(mmio_, 0, 0x12345678);
    EXPECT_ABS_READ32(mmio_, 0, 0x12345678);
    sec_mmio_write32(0, 0x12345678);
    sec_mmio_check_counters(/*expected_check_count=*/0);
  };
  // The developer forgot to increment the write counter, or an attacker
  // glitched the sec write operation.
  ASSERT_DEATH(deadly_ops(), "");
}

}  // namespace
}  // namespace sec_mmio_unittest
