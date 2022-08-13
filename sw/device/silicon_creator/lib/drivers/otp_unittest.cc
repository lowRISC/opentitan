// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/otp.h"

#include <array>

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/silicon_creator/lib/base/mock_sec_mmio.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"  // Generated.

namespace otp_unittest {
namespace {
using ::testing::ElementsAre;
using ::testing::ElementsAreArray;

class OtpTest : public rom_test::RomTest {
 protected:
  uint32_t base_ = TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR;
  rom_test::MockSecMmio mmio_;
};

TEST_F(OtpTest, CreatorSwCfgLockdown) {
  EXPECT_SEC_WRITE32(base_ + OTP_CTRL_CREATOR_SW_CFG_READ_LOCK_REG_OFFSET, 0);

  otp_creator_sw_cfg_lockdown();
}

class OtpReadTest : public OtpTest {
 protected:
  const ptrdiff_t offset_ = OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET;
};

TEST_F(OtpReadTest, Read32) {
  EXPECT_SEC_READ32(base_ + offset_, 0x00010203);

  EXPECT_EQ(otp_read32(0), 0x00010203);
}

TEST_F(OtpReadTest, Read64) {
  EXPECT_SEC_READ32(base_ + offset_ + 8, 0x04050607);
  EXPECT_SEC_READ32(base_ + offset_ + 4, 0x08090A0B);

  EXPECT_EQ(otp_read64(4), 0x0405060708090A0B);
}

TEST_F(OtpReadTest, ReadLen32) {
  EXPECT_SEC_READ32(base_ + offset_, 0x08090A0B);

  uint32_t value = 0;
  otp_read(0, &value, 1);
  EXPECT_EQ(value, 0x08090A0B);
}

TEST_F(OtpReadTest, ReadLen64) {
  EXPECT_SEC_READ32(base_ + offset_, 0x0C0D0E0F);
  EXPECT_SEC_READ32(base_ + offset_ + 4, 0x08090A0B);

  std::array<uint32_t, 2> buf;
  otp_read(0, buf.data(), 2);
  EXPECT_THAT(buf, ElementsAre(0x0C0D0E0F, 0x08090A0B));
}

TEST_F(OtpReadTest, ReadLenN) {
  for (int val = 0; val < 16; ++val) {
    EXPECT_SEC_READ32(base_ + offset_ + val * sizeof(uint32_t), val);
  }

  std::array<uint32_t, 16> arr;
  otp_read(0, arr.data(), arr.size());

  std::array<uint32_t, 16> expected;
  std::iota(expected.begin(), expected.end(), 0);
  EXPECT_THAT(arr, ElementsAreArray(expected));
}

}  // namespace
}  // namespace otp_unittest
