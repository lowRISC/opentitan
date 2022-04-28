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

class InputChangeDetectConfigTest : public SysrstCtrlTest {
 protected:
  dif_sysrst_ctrl_input_change_config_t config_ = {
      .input_changes = kDifSysrstCtrlInputAll,
      .debounce_time_threshold = 0x1000,
  };
};

TEST_F(InputChangeDetectConfigTest, NullArgs) {
  EXPECT_DIF_BADARG(
      dif_sysrst_ctrl_input_change_detect_configure(nullptr, config_));
}

TEST_F(InputChangeDetectConfigTest, BadArgs) {
  // Bad input signal changes.
  config_.input_changes = static_cast<dif_sysrst_ctrl_input_change_t>(1U << 7);
  EXPECT_DIF_BADARG(
      dif_sysrst_ctrl_input_change_detect_configure(&sysrst_ctrl_, config_));
  config_.input_changes = static_cast<dif_sysrst_ctrl_input_change_t>(1U << 15);
  EXPECT_DIF_BADARG(
      dif_sysrst_ctrl_input_change_detect_configure(&sysrst_ctrl_, config_));
}

TEST_F(InputChangeDetectConfigTest, Locked) {
  EXPECT_READ32(SYSRST_CTRL_REGWEN_REG_OFFSET, 0);
  EXPECT_EQ(
      dif_sysrst_ctrl_input_change_detect_configure(&sysrst_ctrl_, config_),
      kDifLocked);
}

TEST_F(InputChangeDetectConfigTest, Success) {
  EXPECT_READ32(SYSRST_CTRL_REGWEN_REG_OFFSET, 1);
  EXPECT_WRITE32(SYSRST_CTRL_KEY_INTR_CTL_REG_OFFSET, config_.input_changes);
  EXPECT_WRITE32(SYSRST_CTRL_KEY_INTR_DEBOUNCE_CTL_REG_OFFSET,
                 config_.debounce_time_threshold);
  EXPECT_DIF_OK(
      dif_sysrst_ctrl_input_change_detect_configure(&sysrst_ctrl_, config_));
}

class OutputPinOverrideConfigTest : public SysrstCtrlTest {
 protected:
  dif_sysrst_ctrl_pin_config_t config_ = {
      .enabled = kDifToggleEnabled,
      .allow_zero = true,
      .allow_one = true,
      .override_value = true,
  };
};

TEST_F(OutputPinOverrideConfigTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_sysrst_ctrl_output_pin_override_configure(
      nullptr, kDifSysrstCtrlPinBatteryDisableOut, config_));
}

TEST_F(OutputPinOverrideConfigTest, BadArgs) {
  // Bad pin.
  EXPECT_DIF_BADARG(dif_sysrst_ctrl_output_pin_override_configure(
      &sysrst_ctrl_, kDifSysrstCtrlPinKey0In, config_));

  // Bad enabled.
  config_.enabled = static_cast<dif_toggle_t>(2);
  EXPECT_DIF_BADARG(dif_sysrst_ctrl_output_pin_override_configure(
      &sysrst_ctrl_, kDifSysrstCtrlPinKey0Out, config_));

  // Bad allow values.
  config_ = {
      .enabled = kDifToggleEnabled,
      .allow_zero = false,
      .allow_one = true,
      .override_value = false,
  };
  EXPECT_DIF_BADARG(dif_sysrst_ctrl_output_pin_override_configure(
      &sysrst_ctrl_, kDifSysrstCtrlPinBatteryDisableOut, config_));
  config_ = {
      .enabled = kDifToggleEnabled,
      .allow_zero = true,
      .allow_one = false,
      .override_value = true,
  };
  EXPECT_DIF_BADARG(dif_sysrst_ctrl_output_pin_override_configure(
      &sysrst_ctrl_, kDifSysrstCtrlPinBatteryDisableOut, config_));
}

TEST_F(OutputPinOverrideConfigTest, Locked) {
  EXPECT_READ32(SYSRST_CTRL_REGWEN_REG_OFFSET, 0);
  EXPECT_EQ(dif_sysrst_ctrl_output_pin_override_configure(
                &sysrst_ctrl_, kDifSysrstCtrlPinBatteryDisableOut, config_),
            kDifLocked);
}

TEST_F(OutputPinOverrideConfigTest, Success) {
  EXPECT_READ32(SYSRST_CTRL_REGWEN_REG_OFFSET, 1);
  EXPECT_READ32(SYSRST_CTRL_PIN_OUT_CTL_REG_OFFSET,
                {{SYSRST_CTRL_PIN_OUT_CTL_Z3_WAKEUP_BIT, 1}});
  EXPECT_WRITE32(SYSRST_CTRL_PIN_OUT_CTL_REG_OFFSET,
                 {{SYSRST_CTRL_PIN_OUT_CTL_BAT_DISABLE_BIT, 1},
                  {SYSRST_CTRL_PIN_OUT_CTL_Z3_WAKEUP_BIT, 1}});
  EXPECT_READ32(SYSRST_CTRL_PIN_OUT_VALUE_REG_OFFSET,
                {{SYSRST_CTRL_PIN_OUT_VALUE_Z3_WAKEUP_BIT, 1}});
  EXPECT_WRITE32(SYSRST_CTRL_PIN_OUT_VALUE_REG_OFFSET,
                 {{SYSRST_CTRL_PIN_OUT_VALUE_BAT_DISABLE_BIT, 1},
                  {SYSRST_CTRL_PIN_OUT_VALUE_Z3_WAKEUP_BIT, 1}});
  EXPECT_READ32(SYSRST_CTRL_PIN_ALLOWED_CTL_REG_OFFSET,
                {{SYSRST_CTRL_PIN_ALLOWED_CTL_Z3_WAKEUP_0_BIT, 1}});
  EXPECT_WRITE32(SYSRST_CTRL_PIN_ALLOWED_CTL_REG_OFFSET,
                 {{SYSRST_CTRL_PIN_ALLOWED_CTL_Z3_WAKEUP_0_BIT, 1},
                  {SYSRST_CTRL_PIN_ALLOWED_CTL_BAT_DISABLE_0_BIT, 1},
                  {SYSRST_CTRL_PIN_ALLOWED_CTL_BAT_DISABLE_1_BIT, 1}});
  EXPECT_DIF_OK(dif_sysrst_ctrl_output_pin_override_configure(
      &sysrst_ctrl_, kDifSysrstCtrlPinBatteryDisableOut, config_));
}

class UlpWakeupConfigTest : public SysrstCtrlTest {
 protected:
  dif_sysrst_ctrl_ulp_wakeup_config_t config_ = {
      .enabled = kDifToggleEnabled,
      .ac_power_debounce_time_threshold = 0x100,
      .lid_open_debounce_time_threshold = 0x200,
      .power_button_debounce_time_threshold = 0x300,
  };
};

TEST_F(UlpWakeupConfigTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_sysrst_ctrl_ulp_wakeup_configure(nullptr, config_));
}

TEST_F(UlpWakeupConfigTest, BadArgs) {
  // Bad enabled.
  config_.enabled = static_cast<dif_toggle_t>(2);
  EXPECT_DIF_BADARG(
      dif_sysrst_ctrl_ulp_wakeup_configure(&sysrst_ctrl_, config_));
}

TEST_F(UlpWakeupConfigTest, Locked) {
  EXPECT_READ32(SYSRST_CTRL_REGWEN_REG_OFFSET, 0);
  EXPECT_EQ(dif_sysrst_ctrl_ulp_wakeup_configure(&sysrst_ctrl_, config_),
            kDifLocked);
}

TEST_F(UlpWakeupConfigTest, Success) {
  EXPECT_READ32(SYSRST_CTRL_REGWEN_REG_OFFSET, 1);
  EXPECT_WRITE32(SYSRST_CTRL_ULP_CTL_REG_OFFSET, 1);
  EXPECT_WRITE32(SYSRST_CTRL_ULP_AC_DEBOUNCE_CTL_REG_OFFSET,
                 config_.ac_power_debounce_time_threshold);
  EXPECT_WRITE32(SYSRST_CTRL_ULP_LID_DEBOUNCE_CTL_REG_OFFSET,
                 config_.lid_open_debounce_time_threshold);
  EXPECT_WRITE32(SYSRST_CTRL_ULP_PWRB_DEBOUNCE_CTL_REG_OFFSET,
                 config_.power_button_debounce_time_threshold);
  EXPECT_DIF_OK(dif_sysrst_ctrl_ulp_wakeup_configure(&sysrst_ctrl_, config_));
}

}  // namespace
}  // namespace dif_sysrst_ctrl_unittest
