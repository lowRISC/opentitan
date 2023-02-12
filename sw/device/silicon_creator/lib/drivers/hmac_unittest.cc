// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/hmac.h"

#include <array>
#include <limits>

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_abs_mmio.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

#include "hmac_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

namespace hmac_unittest {
namespace {
using ::testing::ElementsAreArray;

class HmacTest : public rom_test::RomTest {
 protected:
  uint32_t base_ = TOP_EARLGREY_HMAC_BASE_ADDR;
  rom_test::MockAbsMmio mmio_;
};

class Sha256InitTest : public HmacTest {};

TEST_F(Sha256InitTest, Initialize) {
  EXPECT_ABS_WRITE32(base_ + HMAC_CFG_REG_OFFSET, 0u);
  EXPECT_ABS_WRITE32(base_ + HMAC_INTR_ENABLE_REG_OFFSET, 0u);
  EXPECT_ABS_WRITE32(base_ + HMAC_INTR_STATE_REG_OFFSET,
                     std::numeric_limits<uint32_t>::max());
  EXPECT_ABS_WRITE32(base_ + HMAC_CFG_REG_OFFSET,
                     {
                         {HMAC_CFG_DIGEST_SWAP_BIT, false},
                         {HMAC_CFG_ENDIAN_SWAP_BIT, false},
                         {HMAC_CFG_SHA_EN_BIT, true},
                         {HMAC_CFG_HMAC_EN_BIT, false},
                     });
  EXPECT_ABS_WRITE32(base_ + HMAC_CMD_REG_OFFSET,
                     {{HMAC_CMD_HASH_START_BIT, true}});
  hmac_sha256_init();
}

class Sha256UpdateTest : public HmacTest {};

TEST_F(Sha256UpdateTest, SendData) {
  constexpr std::array<uint8_t, 16> kData = {
      0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
      0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
  };

  // Trigger 8bit aligned writes.
  EXPECT_ABS_WRITE8(base_ + HMAC_MSG_FIFO_REG_OFFSET, 0x01);
  EXPECT_ABS_WRITE8(base_ + HMAC_MSG_FIFO_REG_OFFSET, 0x02);
  hmac_sha256_update(&kData[1], 2);

  // Trigger a single 32bit aligned write.
  EXPECT_ABS_WRITE32(base_ + HMAC_MSG_FIFO_REG_OFFSET, 0x03020100);
  hmac_sha256_update(&kData[0], 4);

  // Trigger 8bit/32bit/8bit sequence.
  EXPECT_ABS_WRITE8(base_ + HMAC_MSG_FIFO_REG_OFFSET, 0x02);
  EXPECT_ABS_WRITE8(base_ + HMAC_MSG_FIFO_REG_OFFSET, 0x03);
  EXPECT_ABS_WRITE32(base_ + HMAC_MSG_FIFO_REG_OFFSET, 0x07060504);
  EXPECT_ABS_WRITE8(base_ + HMAC_MSG_FIFO_REG_OFFSET, 0x08);
  EXPECT_ABS_WRITE8(base_ + HMAC_MSG_FIFO_REG_OFFSET, 0x09);
  hmac_sha256_update(&kData[2], 8);
}

class Sha256FinalTest : public HmacTest {};

TEST_F(Sha256FinalTest, GetDigest) {
  constexpr std::array<uint32_t, 8> kExpectedDigest = {
      0x00000000, 0x11111111, 0x22222222, 0x33333333,
      0x44444444, 0x55555555, 0x66666666, 0x77777777,
  };

  // Request digest.
  EXPECT_ABS_WRITE32(base_ + HMAC_CMD_REG_OFFSET,
                     {{HMAC_CMD_HASH_PROCESS_BIT, true}});

  // Poll a couple of times before returning the result
  EXPECT_ABS_READ32(base_ + HMAC_INTR_STATE_REG_OFFSET,
                    {
                        {HMAC_INTR_STATE_HMAC_DONE_BIT, false},
                    });
  EXPECT_ABS_READ32(base_ + HMAC_INTR_STATE_REG_OFFSET,
                    {
                        {HMAC_INTR_STATE_HMAC_DONE_BIT, true},
                    });
  EXPECT_ABS_WRITE32(base_ + HMAC_INTR_STATE_REG_OFFSET,
                     {
                         {HMAC_INTR_STATE_HMAC_DONE_BIT, true},
                     });

  // Set expectations explicitly to ensure that the registers
  // are contiguous.
  EXPECT_ABS_READ32(base_ + HMAC_DIGEST_7_REG_OFFSET, kExpectedDigest[0]);
  EXPECT_ABS_READ32(base_ + HMAC_DIGEST_6_REG_OFFSET, kExpectedDigest[1]);
  EXPECT_ABS_READ32(base_ + HMAC_DIGEST_5_REG_OFFSET, kExpectedDigest[2]);
  EXPECT_ABS_READ32(base_ + HMAC_DIGEST_4_REG_OFFSET, kExpectedDigest[3]);
  EXPECT_ABS_READ32(base_ + HMAC_DIGEST_3_REG_OFFSET, kExpectedDigest[4]);
  EXPECT_ABS_READ32(base_ + HMAC_DIGEST_2_REG_OFFSET, kExpectedDigest[5]);
  EXPECT_ABS_READ32(base_ + HMAC_DIGEST_1_REG_OFFSET, kExpectedDigest[6]);
  EXPECT_ABS_READ32(base_ + HMAC_DIGEST_0_REG_OFFSET, kExpectedDigest[7]);

  hmac_digest_t got_digest;
  hmac_sha256_final(&got_digest);
  EXPECT_THAT(got_digest.digest, ElementsAreArray(kExpectedDigest));
}

}  // namespace
}  // namespace hmac_unittest
