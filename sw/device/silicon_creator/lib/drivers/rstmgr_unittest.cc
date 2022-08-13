// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_abs_mmio.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "rstmgr_regs.h"  // Generated.

namespace rstmgr_unittest {
namespace {
using ::testing::ElementsAre;

class RstmgrTest : public rom_test::RomTest {
 protected:
  uint32_t base_ = TOP_EARLGREY_RSTMGR_AON_BASE_ADDR;
  rom_test::MockAbsMmio mmio_;
};

TEST_F(RstmgrTest, GetResetReason) {
  EXPECT_ABS_READ32(base_ + RSTMGR_ALERT_INFO_ATTR_REG_OFFSET, 5);

  EXPECT_ABS_WRITE32(base_ + RSTMGR_ALERT_INFO_CTRL_REG_OFFSET, 0x00);
  EXPECT_ABS_READ32(base_ + RSTMGR_ALERT_INFO_REG_OFFSET, 1);
  EXPECT_ABS_WRITE32(base_ + RSTMGR_ALERT_INFO_CTRL_REG_OFFSET, 0x10);
  EXPECT_ABS_READ32(base_ + RSTMGR_ALERT_INFO_REG_OFFSET, 2);
  EXPECT_ABS_WRITE32(base_ + RSTMGR_ALERT_INFO_CTRL_REG_OFFSET, 0x20);
  EXPECT_ABS_READ32(base_ + RSTMGR_ALERT_INFO_REG_OFFSET, 3);
  EXPECT_ABS_WRITE32(base_ + RSTMGR_ALERT_INFO_CTRL_REG_OFFSET, 0x30);
  EXPECT_ABS_READ32(base_ + RSTMGR_ALERT_INFO_REG_OFFSET, 4);
  EXPECT_ABS_WRITE32(base_ + RSTMGR_ALERT_INFO_CTRL_REG_OFFSET, 0x40);
  EXPECT_ABS_READ32(base_ + RSTMGR_ALERT_INFO_REG_OFFSET, 5);

  EXPECT_ABS_READ32(base_ + RSTMGR_RESET_INFO_REG_OFFSET, 0x12345);

  EXPECT_EQ(rstmgr_reason_get(), 0x12345);
  EXPECT_EQ(rstmgr_alert_info.length, 5);
  EXPECT_THAT(rstmgr_alert_info.info,
              ElementsAre(1, 2, 3, 4, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0));
}

TEST_F(RstmgrTest, ClearResetReason) {
  uint32_t mask = 1u << kRstmgrReasonPowerOn;
  EXPECT_ABS_WRITE32(base_ + RSTMGR_RESET_INFO_REG_OFFSET, mask);
  rstmgr_reason_clear(mask);
}

TEST_F(RstmgrTest, EnableAlertInfo) {
  EXPECT_ABS_WRITE32(base_ + RSTMGR_ALERT_INFO_CTRL_REG_OFFSET, 1);
  rstmgr_alert_info_enable();
}

TEST_F(RstmgrTest, Reset) {
  EXPECT_ABS_WRITE32(base_ + RSTMGR_RESET_REQ_REG_OFFSET, kMultiBitBool4True);
  rstmgr_reset();
}

}  // namespace
}  // namespace rstmgr_unittest
