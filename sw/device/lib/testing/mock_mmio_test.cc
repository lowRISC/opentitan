// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/mock_mmio.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"

namespace {
using ::mock_mmio::MmioTest;
using ::testing::Test;

/**
 * Exercises the register |dev| by reading a value at offset 0x0,
 * writing its complement to 0x4, and then writing its upper half
 * and lower half to 0x8 and 0xa.
 */
uint32_t WriteTwice(mmio_region_t dev) {
  auto value = mmio_region_read32(dev, 0x0);
  mmio_region_write32(dev, 0x4, ~value);
  mmio_region_write16(dev, 0x8, value >> 16);
  mmio_region_write16(dev, 0xa, value & 0xffff);
  return value;
}

class WriteTwiceTest : public Test, public MmioTest {};
TEST_F(WriteTwiceTest, WriteTwice) {
  EXPECT_READ32(0x0, 0xdeadbeef);
  EXPECT_WRITE32(0x4, 0x21524110)
  EXPECT_WRITE16(0x8, 0xdead);
  EXPECT_WRITE16(0xa, 0xbeef);

  EXPECT_EQ(WriteTwice(dev().region()), 0xdeadbeef);
}
}  // namespace
