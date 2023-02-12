// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_abs_mmio.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "sram_ctrl_regs.h"  // Generated.

namespace retention_sram_unittest {
namespace {
class RetentionSramTest : public rom_test::RomTest {
 protected:
  uint32_t base_ = TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_BASE_ADDR;
  rom_test::MockAbsMmio mmio_;
};

class ScrambleTest : public RetentionSramTest {};

TEST_F(ScrambleTest, Ok) {
  EXPECT_ABS_WRITE32(base_ + SRAM_CTRL_CTRL_REG_OFFSET,
                     {
                         {SRAM_CTRL_CTRL_RENEW_SCR_KEY_BIT, 1},
                         {SRAM_CTRL_CTRL_INIT_BIT, 1},
                     });

  retention_sram_scramble();
}

class InitTest : public RetentionSramTest {};

TEST_F(InitTest, Ok) {
  EXPECT_ABS_WRITE32(base_ + SRAM_CTRL_CTRL_REG_OFFSET,
                     {
                         {SRAM_CTRL_CTRL_INIT_BIT, 1},
                     });

  retention_sram_init();
}

}  // namespace
}  // namespace retention_sram_unittest
