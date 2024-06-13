// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/otp.h"

#include <array>

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_abs_mmio.h"
#include "sw/device/silicon_creator/lib/base/mock_sec_mmio.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"  // Generated.

namespace otp_unittest {
namespace {
using ::testing::ElementsAre;
using ::testing::ElementsAreArray;

constexpr int kMaxOtpWordsToRead = 10;

class OtpTest : public rom_test::RomTest {
 protected:
  uint32_t base_ = TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR;
  rom_test::MockSecMmio mmio_;
  rom_test::MockAbsMmio abs_mmio_;
};

TEST_F(OtpTest, CreatorSwCfgLockdown) {
  EXPECT_SEC_WRITE32(base_ + OTP_CTRL_CREATOR_SW_CFG_READ_LOCK_REG_OFFSET, 0);

  otp_creator_sw_cfg_lockdown();
}

class OtpReadTest : public OtpTest {
 protected:
  const ptrdiff_t mmap_window_offset_ = OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET;
  void ExpectDaiIdleCheck(bool idle) {
    EXPECT_ABS_READ32(base_ + OTP_CTRL_STATUS_REG_OFFSET,
                      {{OTP_CTRL_STATUS_DAI_IDLE_BIT, idle}});
  }
};

TEST_F(OtpReadTest, Read32) {
  EXPECT_SEC_READ32(base_ + mmap_window_offset_, 0x00010203);

  EXPECT_EQ(otp_read32(0), 0x00010203);
}

TEST_F(OtpReadTest, Read64) {
  EXPECT_SEC_READ32(base_ + mmap_window_offset_ + 8, 0x04050607);
  EXPECT_SEC_READ32(base_ + mmap_window_offset_ + 4, 0x08090A0B);

  EXPECT_EQ(otp_read64(4), 0x0405060708090A0B);
}

TEST_F(OtpReadTest, ReadLen32) {
  EXPECT_SEC_READ32(base_ + mmap_window_offset_, 0x08090A0B);

  uint32_t value = 0;
  otp_read(0, &value, 1);
  EXPECT_EQ(value, 0x08090A0B);
}

TEST_F(OtpReadTest, ReadLen64) {
  EXPECT_SEC_READ32(base_ + mmap_window_offset_, 0x0C0D0E0F);
  EXPECT_SEC_READ32(base_ + mmap_window_offset_ + 4, 0x08090A0B);

  std::array<uint32_t, 2> buf;
  otp_read(0, buf.data(), 2);
  EXPECT_THAT(buf, ElementsAre(0x0C0D0E0F, 0x08090A0B));
}

TEST_F(OtpReadTest, ReadLenN) {
  for (int val = 0; val < 16; ++val) {
    EXPECT_SEC_READ32(base_ + mmap_window_offset_ + val * sizeof(uint32_t),
                      val);
  }

  std::array<uint32_t, 16> arr;
  otp_read(0, arr.data(), arr.size());

  std::array<uint32_t, 16> expected;
  std::iota(expected.begin(), expected.end(), 0);
  EXPECT_THAT(arr, ElementsAreArray(expected));
}

struct DigestReadTestCase {
  otp_partition_t partition;
  uint32_t digest_offest;
};

class OtpPartitionDigestTest
    : public OtpTest,
      public testing::WithParamInterface<DigestReadTestCase> {};

TEST_P(OtpPartitionDigestTest, ReadDigest) {
  EXPECT_SEC_READ32(base_ + GetParam().digest_offest + sizeof(uint32_t),
                    0x12345678);
  EXPECT_SEC_READ32(base_ + GetParam().digest_offest, 0x87654321);
  EXPECT_EQ(otp_partition_digest_read(GetParam().partition),
            0x1234567887654321);
}

INSTANTIATE_TEST_SUITE_P(
    ReadPartitionDigests, OtpPartitionDigestTest,
    testing::Values(
        DigestReadTestCase{
            .partition = kOtpPartitionCreatorSwCfg,
            .digest_offest = OTP_CTRL_CREATOR_SW_CFG_DIGEST_0_REG_OFFSET,
        },
        DigestReadTestCase{
            .partition = kOtpPartitionOwnerSwCfg,
            .digest_offest = OTP_CTRL_OWNER_SW_CFG_DIGEST_0_REG_OFFSET,
        },
        DigestReadTestCase{
            .partition = kOtpPartitionRotCreatorAuthCodesign,
            .digest_offest =
                OTP_CTRL_ROT_CREATOR_AUTH_CODESIGN_DIGEST_0_REG_OFFSET,
        },
        DigestReadTestCase{
            .partition = kOtpPartitionRotCreatorAuthState,
            .digest_offest =
                OTP_CTRL_ROT_CREATOR_AUTH_STATE_DIGEST_0_REG_OFFSET,
        },
        DigestReadTestCase{
            .partition = kOtpPartitionHwCfg0,
            .digest_offest = OTP_CTRL_HW_CFG0_DIGEST_0_REG_OFFSET,
        },
        DigestReadTestCase{
            .partition = kOtpPartitionHwCfg1,
            .digest_offest = OTP_CTRL_HW_CFG1_DIGEST_0_REG_OFFSET,
        }));

class OtpDaiReadTest : public OtpReadTest,
                       public testing::WithParamInterface<int> {};

TEST_F(OtpDaiReadTest, Read32) {
  ExpectDaiIdleCheck(true);
  EXPECT_ABS_WRITE32(base_ + OTP_CTRL_DIRECT_ACCESS_ADDRESS_REG_OFFSET,
                     OTP_CTRL_PARAM_CREATOR_SW_CFG_OFFSET);
  EXPECT_ABS_WRITE32(base_ + OTP_CTRL_DIRECT_ACCESS_CMD_REG_OFFSET, 0x1);
  ExpectDaiIdleCheck(true);
  EXPECT_ABS_READ32(base_ + OTP_CTRL_DIRECT_ACCESS_RDATA_0_REG_OFFSET,
                    0x00010203);
  EXPECT_EQ(otp_dai_read32(kOtpPartitionCreatorSwCfg, 0), 0x00010203);
}

TEST_F(OtpDaiReadTest, Read32WithIdleWait) {
  ExpectDaiIdleCheck(false);
  ExpectDaiIdleCheck(false);
  ExpectDaiIdleCheck(true);
  EXPECT_ABS_WRITE32(base_ + OTP_CTRL_DIRECT_ACCESS_ADDRESS_REG_OFFSET,
                     OTP_CTRL_PARAM_CREATOR_SW_CFG_OFFSET);
  EXPECT_ABS_WRITE32(base_ + OTP_CTRL_DIRECT_ACCESS_CMD_REG_OFFSET, 0x1);
  ExpectDaiIdleCheck(false);
  ExpectDaiIdleCheck(true);
  EXPECT_ABS_READ32(base_ + OTP_CTRL_DIRECT_ACCESS_RDATA_0_REG_OFFSET,
                    0x00010203);
  EXPECT_EQ(otp_dai_read32(kOtpPartitionCreatorSwCfg, 0), 0x00010203);
}

TEST_F(OtpDaiReadTest, Read64) {
  ExpectDaiIdleCheck(true);
  EXPECT_ABS_WRITE32(base_ + OTP_CTRL_DIRECT_ACCESS_ADDRESS_REG_OFFSET,
                     OTP_CTRL_PARAM_OWNER_SW_CFG_OFFSET + 4);
  EXPECT_ABS_WRITE32(base_ + OTP_CTRL_DIRECT_ACCESS_CMD_REG_OFFSET, 0x1);
  ExpectDaiIdleCheck(true);
  EXPECT_ABS_READ32(base_ + OTP_CTRL_DIRECT_ACCESS_RDATA_1_REG_OFFSET,
                    0x00010203);
  EXPECT_ABS_READ32(base_ + OTP_CTRL_DIRECT_ACCESS_RDATA_0_REG_OFFSET,
                    0x00040506);
  EXPECT_EQ(otp_dai_read64(kOtpPartitionOwnerSwCfg, 4), 0x0001020300040506);
}

TEST_F(OtpDaiReadTest, Read64WithIdleWait) {
  ExpectDaiIdleCheck(false);
  ExpectDaiIdleCheck(true);
  EXPECT_ABS_WRITE32(base_ + OTP_CTRL_DIRECT_ACCESS_ADDRESS_REG_OFFSET,
                     OTP_CTRL_PARAM_CREATOR_SW_CFG_OFFSET);
  EXPECT_ABS_WRITE32(base_ + OTP_CTRL_DIRECT_ACCESS_CMD_REG_OFFSET, 0x1);
  ExpectDaiIdleCheck(false);
  ExpectDaiIdleCheck(false);
  ExpectDaiIdleCheck(true);
  EXPECT_ABS_READ32(base_ + OTP_CTRL_DIRECT_ACCESS_RDATA_1_REG_OFFSET,
                    0x00010203);
  EXPECT_ABS_READ32(base_ + OTP_CTRL_DIRECT_ACCESS_RDATA_0_REG_OFFSET,
                    0x00040506);
  EXPECT_EQ(otp_dai_read64(kOtpPartitionCreatorSwCfg, 0), 0x0001020300040506);
}

TEST_P(OtpDaiReadTest, ReadLenN32bitWords) {
  size_t num_words_to_read = GetParam();
  for (size_t i = 0; i < num_words_to_read; ++i) {
    ExpectDaiIdleCheck(true);
    EXPECT_ABS_WRITE32(
        base_ + OTP_CTRL_DIRECT_ACCESS_ADDRESS_REG_OFFSET,
        OTP_CTRL_PARAM_OWNER_SW_CFG_OFFSET + i * sizeof(uint32_t));
    EXPECT_ABS_WRITE32(base_ + OTP_CTRL_DIRECT_ACCESS_CMD_REG_OFFSET, 0x1);
    ExpectDaiIdleCheck(true);
    EXPECT_ABS_READ32(base_ + OTP_CTRL_DIRECT_ACCESS_RDATA_0_REG_OFFSET,
                      0x01020300 + i);
  }

  uint32_t data[kMaxOtpWordsToRead] = {0};
  otp_dai_read(kOtpPartitionOwnerSwCfg, 0, data, num_words_to_read);
  for (size_t i = 0; i < num_words_to_read; ++i) {
    EXPECT_EQ(data[i], 0x01020300 + i);
  }
}

INSTANTIATE_TEST_SUITE_P(Read32bitWordArrays, OtpDaiReadTest,
                         testing::Range(0, kMaxOtpWordsToRead));

}  // namespace
}  // namespace otp_unittest
