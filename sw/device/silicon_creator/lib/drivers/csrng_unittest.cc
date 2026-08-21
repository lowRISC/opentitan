// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/csrng.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mock_abs_mmio.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

#include "csrng_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

namespace csrng_unittest {
namespace {
using ::testing::NotNull;

class CsrngTest : public rom_test::RomTest {
 protected:
  uint32_t base_ = TOP_EARLGREY_CSRNG_BASE_ADDR;
  rom_test::MockAbsMmio mmio_;
};

TEST_F(CsrngTest, Enable) {
  uint32_t expected_ctrl = 0;
  expected_ctrl = bitfield_field32_write(expected_ctrl, CSRNG_CTRL_ENABLE_FIELD,
                                         kMultiBitBool4True);
  expected_ctrl = bitfield_field32_write(
      expected_ctrl, CSRNG_CTRL_SW_APP_ENABLE_FIELD, kMultiBitBool4True);
  expected_ctrl = bitfield_field32_write(
      expected_ctrl, CSRNG_CTRL_READ_INT_STATE_FIELD, kMultiBitBool4True);
  expected_ctrl = bitfield_field32_write(
      expected_ctrl, CSRNG_CTRL_FIPS_FORCE_ENABLE_FIELD, kMultiBitBool4False);

  EXPECT_ABS_WRITE32(base_ + CSRNG_CTRL_REG_OFFSET, expected_ctrl);
  EXPECT_EQ(csrng_enable(), kErrorOk);
}

TEST_F(CsrngTest, InstantiateSuccess) {
  uint32_t expected_ctrl = 0;
  expected_ctrl = bitfield_field32_write(expected_ctrl, CSRNG_CTRL_ENABLE_FIELD,
                                         kMultiBitBool4True);
  expected_ctrl = bitfield_field32_write(
      expected_ctrl, CSRNG_CTRL_SW_APP_ENABLE_FIELD, kMultiBitBool4True);
  expected_ctrl = bitfield_field32_write(
      expected_ctrl, CSRNG_CTRL_READ_INT_STATE_FIELD, kMultiBitBool4True);
  expected_ctrl = bitfield_field32_write(
      expected_ctrl, CSRNG_CTRL_FIPS_FORCE_ENABLE_FIELD, kMultiBitBool4False);

  // csrng_enable() calls
  EXPECT_ABS_WRITE32(base_ + CSRNG_CTRL_REG_OFFSET, expected_ctrl);

  // Poll CMD_RDY -> True
  EXPECT_ABS_READ32(base_ + CSRNG_SW_CMD_STS_REG_OFFSET,
                    1 << CSRNG_SW_CMD_STS_CMD_RDY_BIT);

  // Clear CS_CMD_REQ_DONE bit
  EXPECT_ABS_WRITE32(base_ + CSRNG_INTR_STATE_REG_OFFSET,
                     1 << CSRNG_INTR_STATE_CS_CMD_REQ_DONE_BIT);

  // Command 1 = Instantiate, flag0 = kMultiBitBool4False (0x9)
  uint32_t expected_cmd =
      (1 << 0) | (0 << 4) | (kMultiBitBool4False << 8) | (0 << 12);
  EXPECT_ABS_WRITE32(base_ + CSRNG_CMD_REQ_REG_OFFSET, expected_cmd);

  // Poll CS_CMD_REQ_DONE bit -> True
  EXPECT_ABS_READ32(base_ + CSRNG_INTR_STATE_REG_OFFSET,
                    1 << CSRNG_INTR_STATE_CS_CMD_REQ_DONE_BIT);

  // Check SW_CMD_STS -> 0 (no error)
  EXPECT_ABS_READ32(base_ + CSRNG_SW_CMD_STS_REG_OFFSET, 0);

  EXPECT_EQ(csrng_instantiate(), kErrorOk);
}

TEST_F(CsrngTest, ReadWordsSuccess) {
  // Poll CMD_RDY -> True
  EXPECT_ABS_READ32(base_ + CSRNG_SW_CMD_STS_REG_OFFSET,
                    1 << CSRNG_SW_CMD_STS_CMD_RDY_BIT);

  // Generate 8 words = 2 x 128-bit blocks
  // Command 3 = Generate, flag0 = kMultiBitBool4False (0x9), glen = 2
  uint32_t expected_cmd =
      (3 << 0) | (0 << 4) | (kMultiBitBool4False << 8) | (2 << 12);
  EXPECT_ABS_WRITE32(base_ + CSRNG_CMD_REQ_REG_OFFSET, expected_cmd);

  // Block 0: Poll GENBITS_VLD -> True, then read 4 words
  EXPECT_ABS_READ32(base_ + CSRNG_GENBITS_VLD_REG_OFFSET,
                    1 << CSRNG_GENBITS_VLD_GENBITS_VLD_BIT);
  EXPECT_ABS_READ32(base_ + CSRNG_GENBITS_REG_OFFSET, 0x11111111);
  EXPECT_ABS_READ32(base_ + CSRNG_GENBITS_REG_OFFSET, 0x22222222);
  EXPECT_ABS_READ32(base_ + CSRNG_GENBITS_REG_OFFSET, 0x33333333);
  EXPECT_ABS_READ32(base_ + CSRNG_GENBITS_REG_OFFSET, 0x44444444);

  // Block 1: Poll GENBITS_VLD -> True, then read 4 words
  EXPECT_ABS_READ32(base_ + CSRNG_GENBITS_VLD_REG_OFFSET,
                    1 << CSRNG_GENBITS_VLD_GENBITS_VLD_BIT);
  EXPECT_ABS_READ32(base_ + CSRNG_GENBITS_REG_OFFSET, 0x55555555);
  EXPECT_ABS_READ32(base_ + CSRNG_GENBITS_REG_OFFSET, 0x66666666);
  EXPECT_ABS_READ32(base_ + CSRNG_GENBITS_REG_OFFSET, 0x77777777);
  EXPECT_ABS_READ32(base_ + CSRNG_GENBITS_REG_OFFSET, 0x88888888);

  uint32_t data[8] = {0};
  EXPECT_EQ(csrng_read_words(data, 8), kErrorOk);

  EXPECT_EQ(data[0], 0x11111111);
  EXPECT_EQ(data[1], 0x22222222);
  EXPECT_EQ(data[2], 0x33333333);
  EXPECT_EQ(data[3], 0x44444444);
  EXPECT_EQ(data[4], 0x55555555);
  EXPECT_EQ(data[5], 0x66666666);
  EXPECT_EQ(data[6], 0x77777777);
  EXPECT_EQ(data[7], 0x88888888);
}

TEST_F(CsrngTest, RandomWordSuccess) {
  // Poll CMD_RDY -> True
  EXPECT_ABS_READ32(base_ + CSRNG_SW_CMD_STS_REG_OFFSET,
                    1 << CSRNG_SW_CMD_STS_CMD_RDY_BIT);

  // Generate 1 word = 1 x 128-bit block
  uint32_t expected_cmd =
      (3 << 0) | (0 << 4) | (kMultiBitBool4False << 8) | (1 << 12);
  EXPECT_ABS_WRITE32(base_ + CSRNG_CMD_REQ_REG_OFFSET, expected_cmd);

  // Poll GENBITS_VLD -> True, read 4 words from block (1 used, 3 discarded)
  EXPECT_ABS_READ32(base_ + CSRNG_GENBITS_VLD_REG_OFFSET,
                    1 << CSRNG_GENBITS_VLD_GENBITS_VLD_BIT);
  EXPECT_ABS_READ32(base_ + CSRNG_GENBITS_REG_OFFSET, 0xcafe0001);
  EXPECT_ABS_READ32(base_ + CSRNG_GENBITS_REG_OFFSET, 0x0002);
  EXPECT_ABS_READ32(base_ + CSRNG_GENBITS_REG_OFFSET, 0x0003);
  EXPECT_ABS_READ32(base_ + CSRNG_GENBITS_REG_OFFSET, 0x0004);

  uint32_t val = 0;
  EXPECT_EQ(csrng_read_words(&val, 1), kErrorOk);
  EXPECT_EQ(val, 0xcafe0001);
}

}  // namespace
}  // namespace csrng_unittest
