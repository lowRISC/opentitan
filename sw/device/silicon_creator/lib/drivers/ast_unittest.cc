// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/ast.h"

#include <array>

#include "gtest/gtest.h"
#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/mock_abs_mmio.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/silicon_creator/lib/base/mock_csr.h"
#include "sw/device/silicon_creator/lib/drivers/mock_otp.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"
#include "sensor_ctrl_regs.h"

namespace ast_unittest {
namespace {
using ::testing::Return;
using ::testing::ValuesIn;

class AstTest : public rom_test::RomTest {
 protected:
  /**
   * Sets up expectations to read the STATUS register of sensor_ctrl twice.
   *
   * @param done1 Value of the AST_INIT_DONE bit for the first read.
   * @param done2 Value of the AST_INIT_DONE bit for the second read.
   *
   */
  void ExpectStatusRead(bool done1, bool done2) {
    EXPECT_ABS_READ32(base_ + SENSOR_CTRL_STATUS_REG_OFFSET,
                      {{SENSOR_CTRL_STATUS_AST_INIT_DONE_BIT, done1}});
    EXPECT_ABS_READ32(base_ + SENSOR_CTRL_STATUS_REG_OFFSET,
                      {{SENSOR_CTRL_STATUS_AST_INIT_DONE_BIT, done2}});
  }

  /**
   * Sets up an expectation to read the AST_INIT_EN OTP item.
   *
   * @param val Value to return;
   */
  void ExpectOtpRead(multi_bit_bool_t val) {
    EXPECT_CALL(otp_, read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_AST_INIT_EN_OFFSET))
        .WillOnce(Return(val));
  }

  uint32_t base_ = TOP_EARLGREY_SENSOR_CTRL_BASE_ADDR;
  rom_test::MockAbsMmio mmio_;
  rom_test::MockOtp otp_;
  mock_csr::MockCsr csr_;
};

TEST_F(AstTest, InitDoneTrue) {
  ExpectStatusRead(true, true);

  EXPECT_EQ(ast_init_done(), kHardenedBoolTrue);
}

TEST_F(AstTest, InitDoneFalse) {
  ExpectStatusRead(false, false);

  EXPECT_EQ(ast_init_done(), kHardenedBoolFalse);

  ExpectStatusRead(true, false);

  EXPECT_EQ(ast_init_done(), kHardenedBoolFalse);

  ExpectStatusRead(false, true);

  EXPECT_EQ(ast_init_done(), kHardenedBoolFalse);
}

class AstLcStateTest : public AstTest,
                       public testing::WithParamInterface<lifecycle_state_t> {};

constexpr std::array<lifecycle_state_t, 2> kLcStatesWithoutCheck{
    kLcStateTest,
    kLcStateRma,
};

class AstLcStatesWithoutCheckTest : public AstLcStateTest {};

TEST_P(AstLcStatesWithoutCheckTest, CheckLcSkip) {
  EXPECT_EQ(ast_check(GetParam()), kErrorOk);
}

INSTANTIATE_TEST_SUITE_P(LcStatesWithoutCheck, AstLcStatesWithoutCheckTest,
                         ValuesIn(kLcStatesWithoutCheck));

constexpr std::array<lifecycle_state_t, 3> kLcStatesWithCheck{
    kLcStateDev,
    kLcStateProd,
    kLcStateProdEnd,
};

class AstLcStatesWithCheckTest : public AstLcStateTest {};

TEST_P(AstLcStatesWithCheckTest, CheckOtpSkip) {
  ExpectOtpRead(kMultiBitBool4False);

  EXPECT_EQ(ast_check(GetParam()), kErrorOk);
}

TEST_P(AstLcStatesWithCheckTest, CheckTimeout) {
  ExpectOtpRead(kMultiBitBool4True);
  EXPECT_CSR_WRITE(CSR_REG_MCYCLE, 0);
  EXPECT_CSR_READ(CSR_REG_MCYCLE, 100);
  ExpectStatusRead(false, false);
  EXPECT_CSR_READ(CSR_REG_MCYCLE, kAstCheckPollCpuCycles);
  ExpectStatusRead(false, false);

  EXPECT_EQ(ast_check(GetParam()), kErrorAstInitNotDone);
}

TEST_P(AstLcStatesWithCheckTest, CheckSuccess) {
  ExpectOtpRead(kMultiBitBool4True);
  EXPECT_CSR_WRITE(CSR_REG_MCYCLE, 0);
  EXPECT_CSR_READ(CSR_REG_MCYCLE, 100);
  ExpectStatusRead(false, false);
  EXPECT_CSR_READ(CSR_REG_MCYCLE, kAstCheckPollCpuCycles);
  ExpectStatusRead(true, true);

  EXPECT_EQ(ast_check(GetParam()), kErrorOk);
}

INSTANTIATE_TEST_SUITE_P(LcStatesWithCheck, AstLcStatesWithCheckTest,
                         ValuesIn(kLcStatesWithCheck));

}  // namespace
}  // namespace ast_unittest
