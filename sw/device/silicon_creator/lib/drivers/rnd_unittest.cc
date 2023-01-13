// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include "sw/device/silicon_creator/lib/drivers/rnd.h"

#include <utility>
#include <vector>

#include "gtest/gtest.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/mock_abs_mmio.h"
#include "sw/device/silicon_creator/lib/base/mock_csr.h"
#include "sw/device/silicon_creator/lib/base/mock_sec_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/mock_otp.h"
#include "sw/device/silicon_creator/lib/mock_crc32.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

#include "entropy_src_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"
#include "rv_core_ibex_regs.h"

namespace rnd_unittest {
namespace {
using ::testing::NotNull;
using ::testing::Return;

class RndTest : public rom_test::RomTest {
 protected:
  uint32_t base_rv_ = TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR;
  uint32_t base_es_ = TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR;

  rom_test::MockCrc32 crc32_;
  rom_test::MockAbsMmio mmio_;
  rom_test::MockSecMmio sec_mmio_;
  rom_test::MockOtp otp_;
  mock_csr::MockCsr csr_;
};

TEST_F(RndTest, GetUint32Enabled) {
  EXPECT_CALL(otp_, read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_EN_OFFSET))
      .WillOnce(Return(kHardenedBoolTrue));

  EXPECT_ABS_READ32(base_rv_ + RV_CORE_IBEX_RND_STATUS_REG_OFFSET,
                    {{RV_CORE_IBEX_RND_STATUS_RND_DATA_VALID_BIT, false}});
  EXPECT_ABS_READ32(base_rv_ + RV_CORE_IBEX_RND_STATUS_REG_OFFSET,
                    {{RV_CORE_IBEX_RND_STATUS_RND_DATA_VALID_BIT, true}});
  EXPECT_CSR_READ(CSR_REG_MCYCLE, 67894);
  EXPECT_ABS_READ32(base_rv_ + RV_CORE_IBEX_RND_DATA_REG_OFFSET, 12345);
  EXPECT_EQ(rnd_uint32(), 67894 + 12345);
}

TEST_F(RndTest, GetUint32Disabled) {
  EXPECT_CALL(otp_, read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_EN_OFFSET))
      .WillOnce(Return(kHardenedBoolFalse));

  EXPECT_CSR_READ(CSR_REG_MCYCLE, 978465);
  EXPECT_ABS_READ32(base_rv_ + RV_CORE_IBEX_RND_DATA_REG_OFFSET, 193475837);
  EXPECT_EQ(rnd_uint32(), 978465 + 193475837);
}

struct RndtLcStateTestCfg {
  lifecycle_state_t lc_state;
  bool expect_error_ok;
  bool mismatch_crc_vals;
};

class RndtLcStateTest : public RndTest,
                        public testing::WithParamInterface<RndtLcStateTestCfg> {
 protected:
  void ExpectHealthCfgCrcCheck(lifecycle_state_t lc_state,
                               uint32_t expected_crc, uint32_t otp_crc) {
    std::vector<std::pair<uint32_t, uint32_t>> regs = {
        {ENTROPY_SRC_REPCNT_THRESHOLDS_REG_OFFSET, 0xffffffff},
        {ENTROPY_SRC_REPCNTS_THRESHOLDS_REG_OFFSET, 0xffffffff},
        {ENTROPY_SRC_ADAPTP_HI_THRESHOLDS_REG_OFFSET, 0xffffffff},
        {ENTROPY_SRC_ADAPTP_LO_THRESHOLDS_REG_OFFSET, 0x0},
        {ENTROPY_SRC_BUCKET_THRESHOLDS_REG_OFFSET, 0xffffffff},
        {ENTROPY_SRC_MARKOV_HI_THRESHOLDS_REG_OFFSET, 0xffffffff},
        {ENTROPY_SRC_MARKOV_LO_THRESHOLDS_REG_OFFSET, 0x0},
        {ENTROPY_SRC_EXTHT_HI_THRESHOLDS_REG_OFFSET, 0xffffffff},
        {ENTROPY_SRC_EXTHT_LO_THRESHOLDS_REG_OFFSET, 0x0},
        {ENTROPY_SRC_ALERT_THRESHOLD_REG_OFFSET, 0xfffd0002},
    };
    EXPECT_CALL(crc32_, Init(NotNull()));
    for (auto reg : regs) {
      EXPECT_ABS_READ32(base_es_ + reg.first, reg.second);
      EXPECT_CALL(crc32_, Add32(NotNull(), reg.second));
    }
    EXPECT_CALL(crc32_, Finish(NotNull())).WillOnce(Return(expected_crc));

    // The implementation does not check the OTP value for the following lc
    // state. See implementation for `rnd_health_config_check()`.
    if (lc_state == kLcStateTest) {
      return;
    }

    EXPECT_CALL(
        otp_,
        read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_HEALTH_CONFIG_DIGEST_OFFSET))
        .WillOnce(Return(otp_crc));
  }
};

TEST_P(RndtLcStateTest, HealthCfgCrcEnabled) {
  EXPECT_CALL(otp_, read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_EN_OFFSET))
      .WillOnce(Return(kHardenedBoolTrue));

  enum {
    kExpectedCrcValOk = 0x8264cf75,
    kExpectedCrcValOkOtp = kExpectedCrcValOk ^ kErrorOk,
  };
  ExpectHealthCfgCrcCheck(
      GetParam().lc_state, kExpectedCrcValOk,
      GetParam().mismatch_crc_vals ? 0 : kExpectedCrcValOkOtp);
  rom_error_t got = rnd_health_config_check(GetParam().lc_state);
  if (GetParam().expect_error_ok) {
    EXPECT_EQ(got, kErrorOk);
  } else {
    EXPECT_NE(got, kErrorOk);
  }
}

TEST_P(RndtLcStateTest, HealthCfgCrcDisabled) {
  EXPECT_CALL(otp_, read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_EN_OFFSET))
      .WillOnce(Return(kHardenedBoolFalse));

  EXPECT_EQ(rnd_health_config_check(GetParam().lc_state), kErrorOk);
}

INSTANTIATE_TEST_SUITE_P(NonTestLcStates, RndtLcStateTest,
                         testing::Values(
                             RndtLcStateTestCfg{
                                 .lc_state = kLcStateTest,
                                 .expect_error_ok = true,
                                 .mismatch_crc_vals = false,
                             },
                             RndtLcStateTestCfg{
                                 .lc_state = kLcStateTest,
                                 .expect_error_ok = true,
                                 .mismatch_crc_vals = true,
                             },
                             RndtLcStateTestCfg{
                                 .lc_state = kLcStateDev,
                                 .expect_error_ok = true,
                                 .mismatch_crc_vals = false,
                             },
                             RndtLcStateTestCfg{
                                 .lc_state = kLcStateDev,
                                 .expect_error_ok = false,
                                 .mismatch_crc_vals = true,
                             },
                             RndtLcStateTestCfg{
                                 .lc_state = kLcStateProd,
                                 .expect_error_ok = true,
                                 .mismatch_crc_vals = false,
                             },
                             RndtLcStateTestCfg{
                                 .lc_state = kLcStateProd,
                                 .expect_error_ok = false,
                                 .mismatch_crc_vals = true,
                             },
                             RndtLcStateTestCfg{
                                 .lc_state = kLcStateProdEnd,
                                 .expect_error_ok = true,
                                 .mismatch_crc_vals = false,
                             },
                             RndtLcStateTestCfg{
                                 .lc_state = kLcStateProdEnd,
                                 .expect_error_ok = false,
                                 .mismatch_crc_vals = true,
                             },
                             RndtLcStateTestCfg{
                                 .lc_state = kLcStateRma,
                                 .expect_error_ok = true,
                                 .mismatch_crc_vals = false,
                             },
                             RndtLcStateTestCfg{
                                 .lc_state = kLcStateRma,
                                 .expect_error_ok = false,
                                 .mismatch_crc_vals = true,
                             }));

}  // namespace
}  // namespace rnd_unittest
