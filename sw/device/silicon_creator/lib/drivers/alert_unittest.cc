// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/alert.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_abs_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/mock_otp.h"
#include "sw/device/silicon_creator/lib/mock_crc32.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

#include "alert_handler_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"

namespace alert_unittest {
namespace {
using ::testing::NotNull;
using ::testing::Return;

class AlertTest : public rom_test::RomTest {
 protected:
  uint32_t base_ = TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR;
  rom_test::MockCrc32 crc32_;
  rom_test::MockAbsMmio abs_mmio_;
  rom_test::MockOtp otp_;
};

class InitTest : public AlertTest {};

TEST_F(InitTest, AlertConfigureAlertBadIndex) {
  EXPECT_EQ(alert_configure(ALERT_HANDLER_ALERT_CLASS_SHADOWED_MULTIREG_COUNT,
                            kAlertClassA, kAlertEnableNone),
            kErrorAlertBadIndex);
}

TEST_F(InitTest, AlertConfigureAlertBadClass) {
  EXPECT_EQ(
      alert_configure(0, static_cast<alert_class_t>(-1), kAlertEnableNone),
      kErrorAlertBadClass);
}

TEST_F(InitTest, LocalAlertConfigureAlertBadClass) {
  EXPECT_EQ(alert_local_configure(0, static_cast<alert_class_t>(-1),
                                  kAlertEnableNone),
            kErrorAlertBadClass);
}

TEST_F(InitTest, AlertConfigureAlertBadEnable) {
  // We expect the alert to get configured as class A, but then to
  // experience an error when evaluating the enable parameter.
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_REG_OFFSET, 0);
  EXPECT_EQ(alert_configure(0, kAlertClassA, static_cast<alert_enable_t>(-1)),
            kErrorAlertBadEnable);
}

TEST_F(InitTest, LocalAlertConfigureAlertBadEnable) {
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_REG_OFFSET, 0);
  EXPECT_EQ(
      alert_local_configure(0, kAlertClassA, static_cast<alert_enable_t>(-1)),
      kErrorAlertBadEnable);
}

TEST_F(InitTest, AlertConfigureAlertClassXNoOperation) {
  EXPECT_EQ(alert_configure(0, kAlertClassX, kAlertEnableNone), kErrorOk);
}

TEST_F(InitTest, LocalAlertConfigureAlertClassXNoOperation) {
  EXPECT_EQ(alert_local_configure(0, kAlertClassX, kAlertEnableNone), kErrorOk);
}

TEST_F(InitTest, AlertConfigure0AsClassA) {
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_REG_OFFSET, 0);
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_ALERT_EN_SHADOWED_0_REG_OFFSET, 1);
  EXPECT_EQ(alert_configure(0, kAlertClassA, kAlertEnableEnabled), kErrorOk);
}

TEST_F(InitTest, LocalAlertConfigure0AsClassA) {
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_REG_OFFSET, 0);
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_0_REG_OFFSET, 1);
  EXPECT_EQ(alert_local_configure(0, kAlertClassA, kAlertEnableEnabled),
            kErrorOk);
}

TEST_F(InitTest, AlertConfigure1AsClassB) {
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_ALERT_CLASS_SHADOWED_1_REG_OFFSET, 1);
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_ALERT_EN_SHADOWED_1_REG_OFFSET, 1);
  EXPECT_EQ(alert_configure(1, kAlertClassB, kAlertEnableEnabled), kErrorOk);
}

TEST_F(InitTest, LocalAlertConfigure1AsClassB) {
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_1_REG_OFFSET, 1);
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_1_REG_OFFSET, 1);
  EXPECT_EQ(alert_local_configure(1, kAlertClassB, kAlertEnableEnabled),
            kErrorOk);
}

TEST_F(InitTest, AlertConfigure2AsClassC) {
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_ALERT_CLASS_SHADOWED_2_REG_OFFSET, 2);
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_ALERT_EN_SHADOWED_2_REG_OFFSET, 1);
  EXPECT_EQ(alert_configure(2, kAlertClassC, kAlertEnableEnabled), kErrorOk);
}

TEST_F(InitTest, LocalAlertConfigure2AsClassC) {
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_2_REG_OFFSET, 2);
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_2_REG_OFFSET, 1);
  EXPECT_EQ(alert_local_configure(2, kAlertClassC, kAlertEnableEnabled),
            kErrorOk);
}

TEST_F(InitTest, AlertConfigure3AsClassDLocked) {
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_ALERT_CLASS_SHADOWED_3_REG_OFFSET, 3);
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_ALERT_EN_SHADOWED_3_REG_OFFSET, 1);
  EXPECT_ABS_WRITE32(base_ + ALERT_HANDLER_ALERT_REGWEN_3_REG_OFFSET, 0);
  EXPECT_EQ(alert_configure(3, kAlertClassD, kAlertEnableLocked), kErrorOk);
}

TEST_F(InitTest, LocalAlertConfigure3AsClassDLocked) {
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_3_REG_OFFSET, 3);
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_3_REG_OFFSET, 1);
  EXPECT_ABS_WRITE32(base_ + ALERT_HANDLER_LOC_ALERT_REGWEN_3_REG_OFFSET, 0);
  EXPECT_EQ(alert_local_configure(3, kAlertClassD, kAlertEnableLocked),
            kErrorOk);
}

TEST_F(InitTest, AlertConfigureClassXBadClass) {
  alert_class_config_t config{};
  EXPECT_EQ(alert_class_configure(kAlertClassX, &config), kErrorAlertBadClass);
}

TEST_F(InitTest, AlertConfigureClassAlertBadEnable) {
  alert_class_config_t config{};
  EXPECT_EQ(alert_class_configure(kAlertClassA, &config), kErrorAlertBadEnable);
}

TEST_F(InitTest, AlertConfigureClassAlertBadEscalation) {
  alert_class_config_t config{.enabled = kAlertEnableLocked};
  EXPECT_EQ(alert_class_configure(kAlertClassA, &config),
            kErrorAlertBadEscalation);
}

TEST_F(InitTest, AlertConfigureClassA) {
  alert_class_config_t config = {
      .enabled = kAlertEnableLocked,
      .escalation = kAlertEscalatePhase3,
      .accum_threshold = 1,
      .timeout_cycles = 2,
      .phase_cycles = {1, 10, 100, 1000},
  };
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_CLASSA_CTRL_SHADOWED_REG_OFFSET,
      {
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_BIT, true},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_LOCK_BIT, true},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E3_BIT, true},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E2_BIT, true},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E1_BIT, true},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E0_BIT, true},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E0_OFFSET, 0},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E1_OFFSET, 1},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E2_OFFSET, 2},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E3_OFFSET, 3},
      });
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_CLASSA_ACCUM_THRESH_SHADOWED_REG_OFFSET, 1);
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_CLASSA_TIMEOUT_CYC_SHADOWED_REG_OFFSET, 2);
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_CLASSA_PHASE0_CYC_SHADOWED_REG_OFFSET, 1);
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_CLASSA_PHASE1_CYC_SHADOWED_REG_OFFSET, 10);
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_CLASSA_PHASE2_CYC_SHADOWED_REG_OFFSET, 100);
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_CLASSA_PHASE3_CYC_SHADOWED_REG_OFFSET, 1000);
  EXPECT_ABS_WRITE32(base_ + ALERT_HANDLER_CLASSA_REGWEN_REG_OFFSET, 0);
  EXPECT_EQ(alert_class_configure(kAlertClassA, &config), kErrorOk);
}

TEST_F(InitTest, AlertConfigureClassB) {
  alert_class_config_t config = {
      .enabled = kAlertEnableEnabled,
      .escalation = kAlertEscalatePhase2,
      .accum_threshold = 1,
      .timeout_cycles = 2,
      .phase_cycles = {1, 10, 100, 1000},
  };
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_CLASSB_CTRL_SHADOWED_REG_OFFSET,
      {
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_BIT, true},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_LOCK_BIT, false},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E3_BIT, false},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E2_BIT, true},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E1_BIT, true},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E0_BIT, true},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E0_OFFSET, 0},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E1_OFFSET, 1},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E2_OFFSET, 2},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E3_OFFSET, 3},
      });
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_CLASSB_ACCUM_THRESH_SHADOWED_REG_OFFSET, 1);
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_CLASSB_TIMEOUT_CYC_SHADOWED_REG_OFFSET, 2);
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_CLASSB_PHASE0_CYC_SHADOWED_REG_OFFSET, 1);
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_CLASSB_PHASE1_CYC_SHADOWED_REG_OFFSET, 10);
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_CLASSB_PHASE2_CYC_SHADOWED_REG_OFFSET, 100);
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_CLASSB_PHASE3_CYC_SHADOWED_REG_OFFSET, 1000);
  EXPECT_EQ(alert_class_configure(kAlertClassB, &config), kErrorOk);
}

TEST_F(InitTest, AlertConfigureClassC) {
  alert_class_config_t config = {
      .enabled = kAlertEnableEnabled,
      .escalation = kAlertEscalatePhase1,
      .accum_threshold = 1,
      .timeout_cycles = 2,
      .phase_cycles = {1, 10, 100, 1000},
  };
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_CLASSC_CTRL_SHADOWED_REG_OFFSET,
      {
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_BIT, true},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_LOCK_BIT, false},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E3_BIT, false},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E2_BIT, false},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E1_BIT, true},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E0_BIT, true},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E0_OFFSET, 0},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E1_OFFSET, 1},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E2_OFFSET, 2},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E3_OFFSET, 3},
      });
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_CLASSC_ACCUM_THRESH_SHADOWED_REG_OFFSET, 1);
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_CLASSC_TIMEOUT_CYC_SHADOWED_REG_OFFSET, 2);
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_CLASSC_PHASE0_CYC_SHADOWED_REG_OFFSET, 1);
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_CLASSC_PHASE1_CYC_SHADOWED_REG_OFFSET, 10);
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_CLASSC_PHASE2_CYC_SHADOWED_REG_OFFSET, 100);
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_CLASSC_PHASE3_CYC_SHADOWED_REG_OFFSET, 1000);
  EXPECT_EQ(alert_class_configure(kAlertClassC, &config), kErrorOk);
}

TEST_F(InitTest, AlertConfigureClassD) {
  alert_class_config_t config = {
      .enabled = kAlertEnableEnabled,
      .escalation = kAlertEscalateNone,
      .accum_threshold = 1,
      .timeout_cycles = 2,
      .phase_cycles = {1, 10, 100, 1000},
  };
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_CLASSD_CTRL_SHADOWED_REG_OFFSET,
      {
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_BIT, true},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_LOCK_BIT, false},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E3_BIT, false},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E2_BIT, false},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E1_BIT, false},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E0_BIT, false},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E0_OFFSET, 0},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E1_OFFSET, 1},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E2_OFFSET, 2},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E3_OFFSET, 3},
      });
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_CLASSD_ACCUM_THRESH_SHADOWED_REG_OFFSET, 1);
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_CLASSD_TIMEOUT_CYC_SHADOWED_REG_OFFSET, 2);
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_CLASSD_PHASE0_CYC_SHADOWED_REG_OFFSET, 1);
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_CLASSD_PHASE1_CYC_SHADOWED_REG_OFFSET, 10);
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_CLASSD_PHASE2_CYC_SHADOWED_REG_OFFSET, 100);
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_CLASSD_PHASE3_CYC_SHADOWED_REG_OFFSET, 1000);
  EXPECT_EQ(alert_class_configure(kAlertClassD, &config), kErrorOk);
}

class AlertPingTest : public AlertTest {};

TEST_F(AlertPingTest, EnableSucess) {
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + ALERT_HANDLER_PING_TIMER_EN_SHADOWED_REG_OFFSET, 1);

  EXPECT_ABS_WRITE32(base_ + ALERT_HANDLER_PING_TIMER_REGWEN_REG_OFFSET, 0);

  EXPECT_EQ(alert_ping_enable(), kErrorOk);
}

/**
 * Functor for incrementing an offset by four.
 */
class WordStepper {
 public:
  WordStepper(uint32_t offset) : offset_(offset - sizeof(uint32_t)) {}

  uint32_t operator()() { return offset_ += sizeof(uint32_t); }

 private:
  uint32_t offset_;
};

class AlertConfigCheckTest : public AlertTest {
 protected:
  void ExpectConfigCrc32(uint32_t exp_crc32) {
    std::vector<uint32_t> reg_offsets;
    auto iter = std::back_inserter(reg_offsets);
    std::generate_n(iter, ALERT_HANDLER_ALERT_REGWEN_MULTIREG_COUNT,
                    WordStepper(ALERT_HANDLER_ALERT_REGWEN_0_REG_OFFSET));
    std::generate_n(iter, ALERT_HANDLER_ALERT_EN_SHADOWED_MULTIREG_COUNT,
                    WordStepper(ALERT_HANDLER_ALERT_EN_SHADOWED_0_REG_OFFSET));
    std::generate_n(
        iter, ALERT_HANDLER_ALERT_CLASS_SHADOWED_MULTIREG_COUNT,
        WordStepper(ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_REG_OFFSET));
    std::generate_n(iter, ALERT_HANDLER_LOC_ALERT_REGWEN_MULTIREG_COUNT,
                    WordStepper(ALERT_HANDLER_LOC_ALERT_REGWEN_0_REG_OFFSET));
    std::generate_n(
        iter, ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_MULTIREG_COUNT,
        WordStepper(ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_0_REG_OFFSET));
    std::generate_n(
        iter, ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_MULTIREG_COUNT,
        WordStepper(ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_REG_OFFSET));
    for (size_t klass = 0; klass < ALERT_HANDLER_PARAM_N_CLASSES; ++klass) {
      enum {
        kClassStep = ALERT_HANDLER_CLASSB_REGWEN_REG_OFFSET -
                     ALERT_HANDLER_CLASSA_REGWEN_REG_OFFSET,
      };
      iter = ALERT_HANDLER_CLASSA_REGWEN_REG_OFFSET + kClassStep * klass;
      iter = ALERT_HANDLER_CLASSA_CTRL_SHADOWED_REG_OFFSET + kClassStep * klass;
      iter = ALERT_HANDLER_CLASSA_ACCUM_THRESH_SHADOWED_REG_OFFSET +
             kClassStep * klass;
      iter = ALERT_HANDLER_CLASSA_TIMEOUT_CYC_SHADOWED_REG_OFFSET +
             kClassStep * klass;
      std::generate_n(
          iter, ALERT_HANDLER_PARAM_N_PHASES,
          WordStepper(ALERT_HANDLER_CLASSA_PHASE0_CYC_SHADOWED_REG_OFFSET +
                      kClassStep * klass));
    }

    EXPECT_CALL(crc32_, Init(NotNull()));
    for (uint32_t offset : reg_offsets) {
      EXPECT_ABS_READ32(base_ + offset, offset);
      EXPECT_CALL(crc32_, Add32(NotNull(), offset));
    }
    EXPECT_CALL(crc32_, Finish(NotNull())).WillOnce(Return(exp_crc32));
  }
};

TEST_F(AlertConfigCheckTest, ConfigCrc32) {
  constexpr uint32_t kExpCrc32 = 0xa5a5a5a5;
  ExpectConfigCrc32(kExpCrc32);

  EXPECT_EQ(alert_config_crc32(), kExpCrc32);
}

TEST_F(AlertConfigCheckTest, CheckInTestLcState) {
  constexpr uint32_t kExpCrc32 = 0xa5a5a5a5;
  ExpectConfigCrc32(kExpCrc32);

  EXPECT_EQ(alert_config_check(kLcStateTest), kErrorOk);
}

struct ConfigCheckTestCase {
  lifecycle_state_t lc_state;
  uint32_t otp_offset;
};

class AlertConfigCheckNonTestLcStateTest
    : public AlertConfigCheckTest,
      public testing::WithParamInterface<ConfigCheckTestCase> {};

TEST_P(AlertConfigCheckNonTestLcStateTest, ConfigCheckGood) {
  constexpr uint32_t kExpCrc32 = 0xa5a5a5a5;
  ExpectConfigCrc32(kExpCrc32);
  EXPECT_CALL(otp_, read32(GetParam().otp_offset))
      .WillOnce(Return(kExpCrc32 ^ GetParam().lc_state ^ kErrorOk));

  EXPECT_EQ(alert_config_check(GetParam().lc_state), kErrorOk);
}

TEST_P(AlertConfigCheckNonTestLcStateTest, ConfigCheckBad) {
  constexpr uint32_t kExpCrc32 = 0xa5a5a5a5;
  ExpectConfigCrc32(kExpCrc32);
  EXPECT_CALL(otp_, read32(GetParam().otp_offset))
      .WillOnce(Return((kExpCrc32 ^ 1) ^ GetParam().lc_state ^ kErrorOk));

  EXPECT_EQ(alert_config_check(GetParam().lc_state), kErrorAlertBadCrc32);
}

INSTANTIATE_TEST_SUITE_P(
    NonTestLcStates, AlertConfigCheckNonTestLcStateTest,
    testing::Values(
        ConfigCheckTestCase{
            .lc_state = kLcStateDev,
            .otp_offset =
                OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_ALERT_DIGEST_DEV_OFFSET,
        },
        ConfigCheckTestCase{
            .lc_state = kLcStateProd,
            .otp_offset =
                OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_ALERT_DIGEST_PROD_OFFSET,
        },
        ConfigCheckTestCase{
            .lc_state = kLcStateProdEnd,
            .otp_offset =
                OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_ALERT_DIGEST_PROD_END_OFFSET,
        },
        ConfigCheckTestCase{
            .lc_state = kLcStateRma,
            .otp_offset =
                OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_ALERT_DIGEST_RMA_OFFSET,
        }));

}  // namespace
}  // namespace alert_unittest
