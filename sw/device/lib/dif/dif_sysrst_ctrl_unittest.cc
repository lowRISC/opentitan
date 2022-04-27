// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_sysrst_ctrl.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/testing/mock_mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "sysrst_ctrl_regs.h"  // Generated.

namespace dif_sysrst_ctrl_unittest {
namespace {
using ::mock_mmio::LeInt;
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;

class SysrstCtrlTest : public testing::Test, public MmioTest {
 protected:
  dif_sysrst_ctrl_t sysrst_ctrl_ = {.base_addr = dev().region()};
};

class KeyComboDetectConfigTest : public SysrstCtrlTest {
 protected:
  dif_sysrst_ctrl_key_combo_config_t config_ = {
      .keys = kDifSysrstCtrlKey0 | kDifSysrstCtrlKeyPowerButton,
      .detection_time_threshold = 0x5000,
      .actions = kDifSysrstCtrlKeyComboActionEcReset,
      .embedded_controller_reset_duration = 0x100,
  };
};

TEST_F(KeyComboDetectConfigTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_sysrst_ctrl_key_combo_detect_configure(
      nullptr, kDifSysrstCtrlKeyCombo1, config_));
}

TEST_F(KeyComboDetectConfigTest, BadArgs) {
  // Bad key combination.
  EXPECT_DIF_BADARG(dif_sysrst_ctrl_key_combo_detect_configure(
      &sysrst_ctrl_, kDifSysrstCtrlKeyComboAll, config_));

  // Bad keys.
  config_.keys = 1U << 5;
  EXPECT_DIF_BADARG(dif_sysrst_ctrl_key_combo_detect_configure(
      &sysrst_ctrl_, kDifSysrstCtrlKeyCombo1, config_));

  // Bad actions.
  config_.keys = kDifSysrstCtrlKey0 | kDifSysrstCtrlKeyPowerButton,
  config_.actions = static_cast<dif_sysrst_ctrl_key_combo_action_t>(1U << 5);
  EXPECT_DIF_BADARG(dif_sysrst_ctrl_key_combo_detect_configure(
      &sysrst_ctrl_, kDifSysrstCtrlKeyCombo1, config_));
}

TEST_F(KeyComboDetectConfigTest, Locked) {
  EXPECT_READ32(SYSRST_CTRL_REGWEN_REG_OFFSET, 0);
  EXPECT_EQ(dif_sysrst_ctrl_key_combo_detect_configure(
                &sysrst_ctrl_, kDifSysrstCtrlKeyCombo1, config_),
            kDifLocked);
}

TEST_F(KeyComboDetectConfigTest, SuccessWithoutEcReset) {
  config_.actions = kDifSysrstCtrlKeyComboActionInterrupt |
                    kDifSysrstCtrlKeyComboActionBatteryDisable;

  EXPECT_READ32(SYSRST_CTRL_REGWEN_REG_OFFSET, 1);
  EXPECT_WRITE32(SYSRST_CTRL_COM_SEL_CTL_1_REG_OFFSET, config_.keys);
  EXPECT_WRITE32(SYSRST_CTRL_COM_DET_CTL_1_REG_OFFSET,
                 config_.detection_time_threshold);
  EXPECT_WRITE32(SYSRST_CTRL_COM_OUT_CTL_1_REG_OFFSET, config_.actions);

  EXPECT_DIF_OK(dif_sysrst_ctrl_key_combo_detect_configure(
      &sysrst_ctrl_, kDifSysrstCtrlKeyCombo1, config_));
}

TEST_F(KeyComboDetectConfigTest, SuccessWithEcReset) {
  EXPECT_READ32(SYSRST_CTRL_REGWEN_REG_OFFSET, 1);
  EXPECT_WRITE32(SYSRST_CTRL_COM_SEL_CTL_1_REG_OFFSET, config_.keys);
  EXPECT_WRITE32(SYSRST_CTRL_COM_DET_CTL_1_REG_OFFSET,
                 config_.detection_time_threshold);
  EXPECT_WRITE32(SYSRST_CTRL_COM_OUT_CTL_1_REG_OFFSET, config_.actions);
  EXPECT_WRITE32(SYSRST_CTRL_EC_RST_CTL_REG_OFFSET,
                 config_.embedded_controller_reset_duration);

  EXPECT_DIF_OK(dif_sysrst_ctrl_key_combo_detect_configure(
      &sysrst_ctrl_, kDifSysrstCtrlKeyCombo1, config_));
}

}  // namespace
}  // namespace dif_sysrst_ctrl_unittest
