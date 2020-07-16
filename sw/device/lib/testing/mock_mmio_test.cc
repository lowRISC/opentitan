// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/mock_mmio.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"

namespace {
using ::mock_mmio::LeInt;
using ::mock_mmio::MmioTest;
using ::testing::Test;

/**
 * Exercises the register |dev| by reading a value at offset 0x0,
 * writing its complement to 0x4, and then writing it byte by byte
 * back over itself, from MSB to LSB.
 */
uint32_t WriteTwice(mmio_region_t dev) {
  auto value = mmio_region_read32(dev, 0x0);
  mmio_region_write32(dev, 0x4, ~value);
  mmio_region_write8(dev, 0x12, (value >> 24) & 0xff);
  mmio_region_write8(dev, 0x8, (value >> 16) & 0xff);
  mmio_region_write8(dev, 0x4, (value >> 8) & 0xff);
  mmio_region_write8(dev, 0x0, value & 0xff);
  return value;
}

class MockMmioTest : public Test, public MmioTest {};

TEST_F(MockMmioTest, WriteTwice) {
  EXPECT_READ32(0x0, 0xdeadbeef);
  EXPECT_WRITE32(0x4, 0x21524110);
  EXPECT_WRITE8(0x12, 0xde);
  EXPECT_WRITE8(0x8, 0xad);
  EXPECT_WRITE8(0x4, 0xbe);
  EXPECT_WRITE8(0x0, 0xef);

  EXPECT_EQ(WriteTwice(dev().region()), 0xdeadbeef);
}

// This test mostly exists to guard against |0x0| being interpreted as a NULL
// pointer literal. C++ overloading is unpredictable in choosing between T* and
// int here.
TEST_F(MockMmioTest, ExpectReadZero) {
  EXPECT_READ8(0x0, 0x0);
  EXPECT_EQ(mmio_region_read8(dev().region(), 0x0), 0x0);
}

TEST_F(MockMmioTest, ExpectWithString) {
  EXPECT_READ32(0xc, LeInt("*\0\0*"));
  EXPECT_EQ(mmio_region_read32(dev().region(), 0xc), 0x2a00002a);

  EXPECT_WRITE32(0x12, LeInt("abcd"));
  mmio_region_write32(dev().region(), 0x12, 0x64636261);
}

TEST_F(MockMmioTest, ExpectWithBits) {
  EXPECT_READ8(0xc, {{0x0, false}, {0x1, true}, {0x3, true}});
  EXPECT_EQ(mmio_region_read8(dev().region(), 0xc), 0b1010);

  EXPECT_WRITE32(0x12, {{0x0, 0xfe}, {0x8, 0xca}});
  mmio_region_write32(dev().region(), 0x12, 0xcafe);
}

TEST_F(MockMmioTest, ExpectMask) {
  EXPECT_MASK32(0x8, {
                         {0x0, 0xfff, 0xabc}, {0x10, 0x1, 0x0},
                     });

  auto value = mmio_region_read32(dev().region(), 0x8);
  // Set the first three nybbles.
  value &= ~0xfff;
  value |= 0xabc;
  // Clear the 16th bit.
  value &= ~(1 << 0x10);
  mmio_region_write32(dev().region(), 0x8, value);
}
}  // namespace
