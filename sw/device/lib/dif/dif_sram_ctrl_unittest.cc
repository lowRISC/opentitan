// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_sram_ctrl.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"
#include "sw/device/lib/dif/dif_base.h"

#include "sram_ctrl_regs.h"  // Generated.

namespace dif_sram_ctrl_autogen_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Test;

class SramCtrlTest : public Test, public MmioTest {
 protected:
  dif_sram_ctrl_t sram_ctrl_ = {.base_addr = dev().region()};
};

class InitTest : public SramCtrlTest {};

TEST_F(InitTest, NullArgs) {
  EXPECT_EQ(dif_sram_ctrl_init(dev().region(), nullptr), kDifBadArg);
}

class RequestNewKeyTest : public SramCtrlTest {};

TEST_F(RequestNewKeyTest, NullArgs) {
  EXPECT_EQ(dif_sram_ctrl_request_new_key(nullptr), kDifBadArg);
}

TEST_F(RequestNewKeyTest, Locked) {
  EXPECT_READ32(SRAM_CTRL_CTRL_REGWEN_REG_OFFSET, 0);
  EXPECT_EQ(dif_sram_ctrl_request_new_key(&sram_ctrl_), kDifLocked);
}

TEST_F(RequestNewKeyTest, Success) {
  EXPECT_READ32(SRAM_CTRL_CTRL_REGWEN_REG_OFFSET, 1);
  EXPECT_WRITE32(SRAM_CTRL_CTRL_REG_OFFSET,
                 {{SRAM_CTRL_CTRL_RENEW_SCR_KEY_BIT, true},
                  {SRAM_CTRL_CTRL_INIT_BIT, false}});
  EXPECT_EQ(dif_sram_ctrl_request_new_key(&sram_ctrl_), kDifOk);
}

class GetStatusTest : public SramCtrlTest {};

TEST_F(GetStatusTest, NullArgs) {
  dif_sram_ctrl_status_bitfield_t status;
  EXPECT_EQ(dif_sram_ctrl_get_status(&sram_ctrl_, nullptr), kDifBadArg);
  EXPECT_EQ(dif_sram_ctrl_get_status(nullptr, &status), kDifBadArg);
  EXPECT_EQ(dif_sram_ctrl_get_status(nullptr, nullptr), kDifBadArg);
}

TEST_F(GetStatusTest, SuccessSome) {
  EXPECT_READ32(SRAM_CTRL_STATUS_REG_OFFSET, 0xA5A5A5A5);

  dif_sram_ctrl_status_bitfield_t status = 0;
  EXPECT_EQ(dif_sram_ctrl_get_status(&sram_ctrl_, &status), kDifOk);
  EXPECT_EQ(status, 0xA5A5A5A5);
}

TEST_F(GetStatusTest, SuccessAll) {
  EXPECT_READ32(SRAM_CTRL_STATUS_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());

  dif_sram_ctrl_status_bitfield_t status = 0;
  EXPECT_EQ(dif_sram_ctrl_get_status(&sram_ctrl_, &status), kDifOk);
  EXPECT_EQ(status, std::numeric_limits<uint32_t>::max());
}

TEST_F(GetStatusTest, SuccessNone) {
  EXPECT_READ32(SRAM_CTRL_STATUS_REG_OFFSET, 0);

  dif_sram_ctrl_status_bitfield_t status = std::numeric_limits<uint32_t>::max();
  EXPECT_EQ(dif_sram_ctrl_get_status(&sram_ctrl_, &status), kDifOk);
  EXPECT_EQ(status, 0);
}

}  // namespace
}  // namespace dif_sram_ctrl_autogen_unittest
