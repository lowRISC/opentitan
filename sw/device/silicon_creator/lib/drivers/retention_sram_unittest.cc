// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_abs_mmio.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "sram_ctrl_regs.h"  // Generated.

namespace retention_sram_unittest {
namespace {
class RetentionSramTest : public mask_rom_test::MaskRomTest {
 protected:
  uint32_t base_ = TOP_EARLGREY_PINMUX_AON_BASE_ADDR;
  mask_rom_test::MockAbsMmio mmio_;
};

class ScrambleTest : public RetentionSramTest {};

TEST_F(ScrambleTest, Ok) {
  uint32_t write_enabled =
      bitfield_bit32_write(0, SRAM_CTRL_CTRL_REGWEN_CTRL_REGWEN_BIT, true);
  EXPECT_ABS_READ32(TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_BASE_ADDR +
                        SRAM_CTRL_CTRL_REGWEN_REG_OFFSET,
                    write_enabled);

  uint32_t ctrl = 0;
  ctrl = bitfield_bit32_write(ctrl, SRAM_CTRL_CTRL_RENEW_SCR_KEY_BIT, true);
  ctrl = bitfield_bit32_write(ctrl, SRAM_CTRL_CTRL_INIT_BIT, true);
  EXPECT_ABS_WRITE32(
      TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_BASE_ADDR + SRAM_CTRL_CTRL_REG_OFFSET,
      ctrl);

  EXPECT_EQ(retention_sram_scramble(), kErrorOk);
}

TEST_F(ScrambleTest, Locked) {
  uint32_t write_enabled =
      bitfield_bit32_write(0, SRAM_CTRL_CTRL_REGWEN_CTRL_REGWEN_BIT, false);
  EXPECT_ABS_READ32(TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_BASE_ADDR +
                        SRAM_CTRL_CTRL_REGWEN_REG_OFFSET,
                    write_enabled);

  EXPECT_EQ(retention_sram_scramble(), kErrorRetSramLocked);
}

}  // namespace
}  // namespace retention_sram_unittest
