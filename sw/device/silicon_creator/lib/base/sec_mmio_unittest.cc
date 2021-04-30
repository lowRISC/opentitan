// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/base/sec_mmio.h"

#include <array>
#include <vector>

#include "gtest/gtest.h"
#include "sw/device/silicon_creator/lib/base/mock_rom_mmio.h"

extern "C" {
// This is an extern in the sec_mmio module.
sec_mmio_ctx_t sec_mmio_ctx;

// FIXME: Replace for shutdown Mock function.
uint32_t __shutdown_count;
}

namespace sec_mmio_unittest {
namespace {
using ::testing::Each;
using ::testing::Eq;
using ::testing::Test;

class SecMmioTest : public Test {
 protected:
  void SetUp() override {
    *shutdown_count_ = 0;
    sec_mmio_init(+[] { ++__shutdown_count; });
  }

  uint32_t GetShutDownCount() { return *shutdown_count_; }

  sec_mmio_ctx_t *ctx_ = &::sec_mmio_ctx;
  uint32_t *shutdown_count_ = &::__shutdown_count;
  mask_rom_test::MockMmio mmio_;
};

TEST_F(SecMmioTest, Initialize) {
  EXPECT_EQ(ctx_->check_count, 0);
  EXPECT_EQ(ctx_->expected_write_count, 0);
  EXPECT_EQ(ctx_->last_index, 0);
  EXPECT_EQ(ctx_->write_count, 0);
  EXPECT_THAT(ctx_->addrs, Each(Eq(UINT32_MAX)));
}

TEST_F(SecMmioTest, Read32OrDie) {
  EXPECT_MMIO_READ32(mmio_, 0, 0x12345678);
  EXPECT_MMIO_READ32(mmio_, 0, 0x12345678);
  EXPECT_EQ(sec_mmio_read32(0), 0x12345678);

  EXPECT_MMIO_READ32(mmio_, 4, 0x87654321);
  EXPECT_MMIO_READ32(mmio_, 4, 0x87654321);
  EXPECT_EQ(sec_mmio_read32(4), 0x87654321);

  EXPECT_MMIO_READ32(mmio_, 0, 0x87654321);
  EXPECT_MMIO_READ32(mmio_, 0, 0x87654321);
  EXPECT_EQ(sec_mmio_read32(0), 0x87654321);

  // Two of the operations were targeting the same offset, so we only expect two
  // operations and zero shutdown attempts.
  EXPECT_EQ(ctx_->write_count, 0);
  EXPECT_EQ(GetShutDownCount(), 0);
  EXPECT_EQ(ctx_->last_index, 2);
}

TEST_F(SecMmioTest, Read32ORDieSimulatedFault) {
  EXPECT_MMIO_READ32(mmio_, 0, 0x12345678);
  EXPECT_MMIO_READ32(mmio_, 0, 0);
  EXPECT_EQ(sec_mmio_read32(0), 0x12345678);
  EXPECT_EQ(ctx_->write_count, 0);
  EXPECT_EQ(GetShutDownCount(), 1);
}

TEST_F(SecMmioTest, Write32) {
  EXPECT_MMIO_WRITE32(mmio_, 0, 0x12345678);
  EXPECT_MMIO_READ32(mmio_, 0, 0x12345678);
  sec_mmio_write32(0, 0x12345678);
  EXPECT_EQ(ctx_->write_count, 1);

  EXPECT_MMIO_WRITE32(mmio_, 4, 0x87654321);
  EXPECT_MMIO_READ32(mmio_, 4, 0x87654321);
  sec_mmio_write32(4, 0x87654321);
  EXPECT_EQ(ctx_->write_count, 2);

  EXPECT_MMIO_WRITE32(mmio_, 0, 0x87654321);
  EXPECT_MMIO_READ32(mmio_, 0, 0x87654321);
  sec_mmio_write32(0, 0x87654321);
  EXPECT_EQ(ctx_->write_count, 3);

  // Two of the operations were targeting the same offset, so we only expect two
  // operations and zero shutdown attempts.
  EXPECT_EQ(GetShutDownCount(), 0);
  EXPECT_EQ(ctx_->last_index, 2);
}

TEST_F(SecMmioTest, Write32SimulatedFault) {
  EXPECT_MMIO_WRITE32(mmio_, 0, 0x12345678);
  EXPECT_MMIO_READ32(mmio_, 0, 0);
  sec_mmio_write32(0, 0x12345678);
  EXPECT_EQ(GetShutDownCount(), 1);
}

TEST_F(SecMmioTest, CounterInc) {
  sec_mmio_write_increment(5);
  EXPECT_EQ(ctx_->expected_write_count, 5);

  sec_mmio_write_increment(10);
  EXPECT_EQ(ctx_->expected_write_count, 15);
}

TEST_F(SecMmioTest, CheckValues) {
  EXPECT_MMIO_WRITE32(mmio_, 0, 0x12345678);
  EXPECT_MMIO_READ32(mmio_, 0, 0x12345678);
  sec_mmio_write32(0, 0x12345678);

  EXPECT_MMIO_READ32(mmio_, 0, 0x12345678);
  sec_mmio_check_values(/*rnd_offset=*/0);
  EXPECT_EQ(ctx_->check_count, 1);
  EXPECT_EQ(GetShutDownCount(), 0);
}

TEST_F(SecMmioTest, CheckValuesSimlatedFault) {
  EXPECT_MMIO_WRITE32(mmio_, 0, 0x12345678);
  EXPECT_MMIO_READ32(mmio_, 0, 0x12345678);
  sec_mmio_write32(0, 0x12345678);

  EXPECT_MMIO_READ32(mmio_, 0, 0);
  sec_mmio_check_values(/*rnd_offset=*/0);
  EXPECT_EQ(GetShutDownCount(), 1);
}

TEST_F(SecMmioTest, CheckCount) {
  EXPECT_MMIO_WRITE32(mmio_, 0, 0x12345678);
  EXPECT_MMIO_READ32(mmio_, 0, 0x12345678);
  sec_mmio_write32(0, 0x12345678);
  sec_mmio_write_increment(1);

  sec_mmio_check_counters(/*expected_check_count=*/0);
  sec_mmio_check_counters(/*expected_check_count=*/1);
  EXPECT_EQ(ctx_->check_count, 2);
  EXPECT_EQ(GetShutDownCount(), 0);
}

TEST_F(SecMmioTest, CheckCountWriteMismatch) {
  EXPECT_MMIO_WRITE32(mmio_, 0, 0x12345678);
  EXPECT_MMIO_READ32(mmio_, 0, 0x12345678);
  sec_mmio_write32(0, 0x12345678);

  // The developer forgot to increment the write counter, or an attacker
  // glitched the sec write operation.
  sec_mmio_check_counters(/*expected_check_count=*/0);

  // The count is incremented twice per sec_mmio_check_counters call
  // on any failure condition due to redundant result checks.
  EXPECT_EQ(GetShutDownCount(), 2);
}

}  // namespace
}  // namespace sec_mmio_unittest
