// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/rnd.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/testing/mock_abs_mmio.h"
#include "sw/device/silicon_creator/lib/base/mock_csr.h"
#include "sw/device/silicon_creator/lib/base/mock_sec_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/mock_otp.h"
#include "sw/device/silicon_creator/testing/mask_rom_test.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"
#include "rv_core_ibex_regs.h"

namespace rnd_unittest {
namespace {
using ::testing::Return;

class RndTest : public mask_rom_test::MaskRomTest {
 protected:
  uint32_t base_ = TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR;

  mask_rom_test::MockAbsMmio mmio_;
  mask_rom_test::MockSecMmio sec_mmio_;
  mask_rom_test::MockOtp otp_;
  mock_csr::MockCsr csr_;
};

TEST_F(RndTest, GetUint32Disabled) {
  EXPECT_CALL(otp_, read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_EN_OFFSET))
      .WillOnce(Return(kHardenedBoolTrue));

  EXPECT_ABS_READ32(base_ + RV_CORE_IBEX_RND_STATUS_REG_OFFSET,
                    {{RV_CORE_IBEX_RND_STATUS_RND_DATA_VALID_BIT, false}});
  EXPECT_ABS_READ32(base_ + RV_CORE_IBEX_RND_STATUS_REG_OFFSET,
                    {{RV_CORE_IBEX_RND_STATUS_RND_DATA_VALID_BIT, true}});
  EXPECT_CSR_READ(CSR_REG_MCYCLE, 67894);
  EXPECT_ABS_READ32(base_ + RV_CORE_IBEX_RND_DATA_REG_OFFSET, 12345);
  EXPECT_EQ(rnd_uint32(), 67894 + 12345);
}

TEST_F(RndTest, GetUint32Enabled) {
  EXPECT_CALL(otp_, read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_EN_OFFSET))
      .WillOnce(Return(kHardenedBoolFalse));

  EXPECT_CSR_READ(CSR_REG_MCYCLE, 978465);
  EXPECT_ABS_READ32(base_ + RV_CORE_IBEX_RND_DATA_REG_OFFSET, 193475837);
  EXPECT_EQ(rnd_uint32(), 978465 + 193475837);
}

}  // namespace
}  // namespace rnd_unittest
