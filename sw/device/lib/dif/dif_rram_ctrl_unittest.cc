// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_rram_ctrl.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "hw/top/rram_ctrl_regs.h"  // Generated.

namespace dif_rram_ctrl_unittest {
namespace {
using mock_mmio::MmioTest;
using mock_mmio::MockDevice;
using testing::Test;

class RramCtrlTest : public Test, public MmioTest {
 protected:
  void SetUp() {
    ASSERT_DIF_OK(dif_rram_ctrl_init_state(&dif_rram_ctrl_, dev().region()));
  }

  dif_rram_ctrl_state_t dif_rram_ctrl_;
};

TEST_F(RramCtrlTest, SimpleQueries) {
  uint32_t scratch;
  EXPECT_READ32(RRAM_CTRL_SCRATCH_REG_OFFSET, 0x89abcdefu);
  EXPECT_DIF_OK(dif_rram_ctrl_get_scratch(&dif_rram_ctrl_, &scratch));
  EXPECT_EQ(scratch, 0x89abcdefu);
}

// TODO: add more tests

}  // namespace
}  // namespace dif_rram_ctrl_unittest
