// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/otp.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "otp_ctrl_regs.h"  // Generated.

namespace otp_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::testing::Test;

class OtpTest : public Test, public MmioTest {
 protected:
  otp_t otp_ = {.base_addr = dev().region()};
};

class OtpReadTest : public OtpTest {
 protected:
  const ptrdiff_t offset_ = OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET;
};

TEST_F(OtpReadTest, Read32) {
  EXPECT_READ32(offset_, 0x00010203);

  EXPECT_EQ(otp_read32(&otp_, 0), 0x00010203);
}

TEST_F(OtpReadTest, Read64) {
  EXPECT_READ32(offset_ + 8, 0x04050607);
  EXPECT_READ32(offset_ + 4, 0x08090A0B);

  EXPECT_EQ(otp_read64(&otp_, 4), 0x0405060708090A0B);
}

TEST_F(OtpReadTest, ReadLen32) {
  EXPECT_READ32(offset_, 0x08090A0B);

  uint32_t value = 0;
  otp_read(&otp_, 0, &value, sizeof(value));
  EXPECT_EQ(value, 0x08090A0B);
}

TEST_F(OtpReadTest, ReadLen64) {
  EXPECT_READ32(offset_, 0x0C0D0E0F);
  EXPECT_READ32(offset_ + 4, 0x08090A0B);

  uint64_t value = 0;
  otp_read(&otp_, 0, &value, sizeof(value));
  EXPECT_EQ(value, 0x08090A0B0C0D0E0F);
}

TEST_F(OtpReadTest, ReadLenN) {
  for (int val = 0; val < 16; ++val) {
    EXPECT_READ32(offset_ + val * sizeof(uint32_t), val);
  }

  std::vector<uint32_t> arr(16);
  otp_read(&otp_, 0, &arr[0], arr.size() * sizeof(uint32_t));

  for (int i = 0; i < arr.size(); ++i) {
    EXPECT_EQ(arr[i], i);
  }
}

}  // namespace
}  // namespace otp_unittest
