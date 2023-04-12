// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_adc_ctrl.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "adc_ctrl_regs.h"  // Generated.

namespace dif_adc_ctrl_unittest {
namespace {
using ::mock_mmio::LeInt;
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;

class AdcCtrlTest : public testing::Test, public MmioTest {
 protected:
  dif_adc_ctrl_t adc_ctrl_ = {.base_addr = dev().region()};
  dif_adc_ctrl_config_t config_ = {
      .mode = kDifAdcCtrlLowPowerScanMode,
      .power_up_time_aon_cycles = 8,
      .wake_up_time_aon_cycles = 128,
      .num_low_power_samples = 4,
      .num_normal_power_samples = 32,
  };
  dif_adc_ctrl_filter_config_t filter_config_ = {
      .filter = kDifAdcCtrlFilter2,
      .min_voltage = 512,
      .max_voltage = 768,
      .in_range = true,
      .generate_wakeup_on_match = true,
      .generate_irq_on_match = true,
  };
};

class ConfigTest : public AdcCtrlTest {};

TEST_F(ConfigTest, NullHandle) {
  EXPECT_DIF_BADARG(dif_adc_ctrl_configure(nullptr, config_));
}

TEST_F(ConfigTest, BadMode) {
  config_.mode = static_cast<dif_adc_ctrl_mode_t>(3);
  EXPECT_DIF_BADARG(dif_adc_ctrl_configure(&adc_ctrl_, config_));
}

TEST_F(ConfigTest, BadPowerUpTime) {
  config_.power_up_time_aon_cycles = ADC_CTRL_ADC_PD_CTL_PWRUP_TIME_MASK + 1;
  EXPECT_DIF_BADARG(dif_adc_ctrl_configure(&adc_ctrl_, config_));
}

TEST_F(ConfigTest, BadWakeUpTime) {
  config_.wake_up_time_aon_cycles = ADC_CTRL_ADC_PD_CTL_WAKEUP_TIME_MASK + 1;
  EXPECT_DIF_BADARG(dif_adc_ctrl_configure(&adc_ctrl_, config_));
}

TEST_F(ConfigTest, BadNumLowPowerSamples) {
  config_.num_low_power_samples = 0;
  EXPECT_DIF_BADARG(dif_adc_ctrl_configure(&adc_ctrl_, config_));
}

TEST_F(ConfigTest, BadNumNormalPowerSamples) {
  config_.num_normal_power_samples = 0;
  EXPECT_DIF_BADARG(dif_adc_ctrl_configure(&adc_ctrl_, config_));
}

TEST_F(ConfigTest, LowPowerModeSuccess) {
  EXPECT_WRITE32(ADC_CTRL_ADC_EN_CTL_REG_OFFSET, 0);
  EXPECT_WRITE32(ADC_CTRL_ADC_PD_CTL_REG_OFFSET,
                 {{ADC_CTRL_ADC_PD_CTL_WAKEUP_TIME_OFFSET,
                   config_.wake_up_time_aon_cycles},
                  {ADC_CTRL_ADC_PD_CTL_PWRUP_TIME_OFFSET,
                   config_.power_up_time_aon_cycles},
                  {ADC_CTRL_ADC_PD_CTL_LP_MODE_BIT, 1}});
  EXPECT_WRITE32(ADC_CTRL_ADC_LP_SAMPLE_CTL_REG_OFFSET,
                 {{ADC_CTRL_ADC_LP_SAMPLE_CTL_LP_SAMPLE_CNT_OFFSET,
                   config_.num_low_power_samples}});
  EXPECT_WRITE32(ADC_CTRL_ADC_SAMPLE_CTL_REG_OFFSET,
                 {{ADC_CTRL_ADC_SAMPLE_CTL_NP_SAMPLE_CNT_OFFSET,
                   config_.num_normal_power_samples}});
  EXPECT_DIF_OK(dif_adc_ctrl_configure(&adc_ctrl_, config_));
}

TEST_F(ConfigTest, NormalPowerModeSuccess) {
  config_.mode = kDifAdcCtrlNormalPowerScanMode;
  EXPECT_WRITE32(ADC_CTRL_ADC_EN_CTL_REG_OFFSET, 0);
  EXPECT_WRITE32(ADC_CTRL_ADC_PD_CTL_REG_OFFSET,
                 {{ADC_CTRL_ADC_PD_CTL_PWRUP_TIME_OFFSET,
                   config_.power_up_time_aon_cycles},
                  {ADC_CTRL_ADC_PD_CTL_WAKEUP_TIME_OFFSET, 0x640}});
  EXPECT_WRITE32(ADC_CTRL_ADC_LP_SAMPLE_CTL_REG_OFFSET,
                 ADC_CTRL_ADC_LP_SAMPLE_CTL_REG_RESVAL);
  EXPECT_WRITE32(ADC_CTRL_ADC_SAMPLE_CTL_REG_OFFSET,
                 {{ADC_CTRL_ADC_SAMPLE_CTL_NP_SAMPLE_CNT_OFFSET,
                   config_.num_normal_power_samples}});
  EXPECT_DIF_OK(dif_adc_ctrl_configure(&adc_ctrl_, config_));
}

TEST_F(ConfigTest, OneshotModeSuccess) {
  config_.mode = kDifAdcCtrlOneshotMode;
  EXPECT_WRITE32(ADC_CTRL_ADC_EN_CTL_REG_OFFSET,
                 {{ADC_CTRL_ADC_EN_CTL_ONESHOT_MODE_BIT, true}});
  EXPECT_WRITE32(ADC_CTRL_ADC_PD_CTL_REG_OFFSET,
                 {{ADC_CTRL_ADC_PD_CTL_PWRUP_TIME_OFFSET,
                   config_.power_up_time_aon_cycles},
                  {ADC_CTRL_ADC_PD_CTL_WAKEUP_TIME_OFFSET, 0x640}});
  EXPECT_WRITE32(ADC_CTRL_ADC_LP_SAMPLE_CTL_REG_OFFSET,
                 ADC_CTRL_ADC_LP_SAMPLE_CTL_REG_RESVAL);
  EXPECT_WRITE32(ADC_CTRL_ADC_SAMPLE_CTL_REG_OFFSET,
                 ADC_CTRL_ADC_SAMPLE_CTL_REG_RESVAL);
  EXPECT_DIF_OK(dif_adc_ctrl_configure(&adc_ctrl_, config_));
}

class FilterConfigTest : public AdcCtrlTest {};

TEST_F(FilterConfigTest, NullHandle) {
  EXPECT_DIF_BADARG(dif_adc_ctrl_configure_filter(
      nullptr, kDifAdcCtrlChannel0, filter_config_, kDifToggleEnabled));
}

TEST_F(FilterConfigTest, BadMinVoltage) {
  filter_config_.min_voltage = 1024;
  EXPECT_DIF_BADARG(dif_adc_ctrl_configure_filter(
      &adc_ctrl_, kDifAdcCtrlChannel0, filter_config_, kDifToggleEnabled));
}

TEST_F(FilterConfigTest, BadMaxVoltage) {
  filter_config_.max_voltage = 1024;
  EXPECT_DIF_BADARG(dif_adc_ctrl_configure_filter(
      &adc_ctrl_, kDifAdcCtrlChannel0, filter_config_, kDifToggleEnabled));
}

TEST_F(FilterConfigTest, BadChannel) {
  EXPECT_DIF_BADARG(dif_adc_ctrl_configure_filter(
      &adc_ctrl_,
      static_cast<dif_adc_ctrl_channel_t>(ADC_CTRL_PARAM_NUM_ADC_CHANNEL),
      filter_config_, kDifToggleEnabled));
}

TEST_F(FilterConfigTest, BadFilter) {
  filter_config_.filter =
      static_cast<dif_adc_ctrl_filter_t>(ADC_CTRL_PARAM_NUM_ADC_FILTER);
  EXPECT_DIF_BADARG(dif_adc_ctrl_configure_filter(
      &adc_ctrl_, kDifAdcCtrlChannel0, filter_config_, kDifToggleEnabled));
  EXPECT_DIF_BADARG(dif_adc_ctrl_configure_filter(
      &adc_ctrl_, kDifAdcCtrlChannel1, filter_config_, kDifToggleEnabled));
}

TEST_F(FilterConfigTest, Success) {
  EXPECT_WRITE32(ADC_CTRL_ADC_CHN1_FILTER_CTL_2_REG_OFFSET,
                 {{ADC_CTRL_ADC_CHN1_FILTER_CTL_2_MIN_V_2_OFFSET,
                   filter_config_.min_voltage},
                  {ADC_CTRL_ADC_CHN1_FILTER_CTL_2_MAX_V_2_OFFSET,
                   filter_config_.max_voltage},
                  {ADC_CTRL_ADC_CHN1_FILTER_CTL_2_COND_2_BIT, false},
                  {ADC_CTRL_ADC_CHN1_FILTER_CTL_2_EN_2_BIT, true}});
  EXPECT_READ32(ADC_CTRL_ADC_WAKEUP_CTL_REG_OFFSET, 0);
  EXPECT_WRITE32(ADC_CTRL_ADC_WAKEUP_CTL_REG_OFFSET,
                 {{filter_config_.filter, true}});
  EXPECT_READ32(ADC_CTRL_ADC_INTR_CTL_REG_OFFSET, 0);
  EXPECT_WRITE32(ADC_CTRL_ADC_INTR_CTL_REG_OFFSET,
                 {{filter_config_.filter, true}});
  EXPECT_DIF_OK(dif_adc_ctrl_configure_filter(
      &adc_ctrl_, kDifAdcCtrlChannel1, filter_config_, kDifToggleEnabled));

  EXPECT_WRITE32(ADC_CTRL_ADC_CHN0_FILTER_CTL_6_REG_OFFSET,
                 {{ADC_CTRL_ADC_CHN0_FILTER_CTL_6_MIN_V_6_OFFSET,
                   filter_config_.min_voltage},
                  {ADC_CTRL_ADC_CHN0_FILTER_CTL_6_MAX_V_6_OFFSET,
                   filter_config_.max_voltage},
                  {ADC_CTRL_ADC_CHN0_FILTER_CTL_6_COND_6_BIT, false},
                  {ADC_CTRL_ADC_CHN0_FILTER_CTL_6_EN_6_BIT, true}});
  EXPECT_READ32(ADC_CTRL_ADC_WAKEUP_CTL_REG_OFFSET, 0x4);
  EXPECT_WRITE32(ADC_CTRL_ADC_WAKEUP_CTL_REG_OFFSET, 0x44);
  EXPECT_READ32(ADC_CTRL_ADC_INTR_CTL_REG_OFFSET, 0x4);
  EXPECT_WRITE32(ADC_CTRL_ADC_INTR_CTL_REG_OFFSET, 0x44);
  filter_config_.filter = kDifAdcCtrlFilter6;
  EXPECT_DIF_OK(dif_adc_ctrl_configure_filter(
      &adc_ctrl_, kDifAdcCtrlChannel0, filter_config_, kDifToggleEnabled));
}

class SetEnabledTest : public AdcCtrlTest {};

TEST_F(SetEnabledTest, NullHandle) {
  EXPECT_DIF_BADARG(dif_adc_ctrl_set_enabled(nullptr, kDifToggleEnabled));
}

TEST_F(SetEnabledTest, BadArgs) {
  EXPECT_DIF_BADARG(
      dif_adc_ctrl_set_enabled(&adc_ctrl_, static_cast<dif_toggle_t>(2)));
}

TEST_F(SetEnabledTest, Success) {
  EXPECT_READ32(ADC_CTRL_ADC_EN_CTL_REG_OFFSET, 0);
  EXPECT_WRITE32(ADC_CTRL_ADC_EN_CTL_REG_OFFSET,
                 {{ADC_CTRL_ADC_EN_CTL_ADC_ENABLE_BIT, true}});
  EXPECT_DIF_OK(dif_adc_ctrl_set_enabled(&adc_ctrl_, kDifToggleEnabled));

  EXPECT_READ32(ADC_CTRL_ADC_EN_CTL_REG_OFFSET,
                {{ADC_CTRL_ADC_EN_CTL_ONESHOT_MODE_BIT, true},
                 {ADC_CTRL_ADC_EN_CTL_ADC_ENABLE_BIT, true}});
  EXPECT_WRITE32(ADC_CTRL_ADC_EN_CTL_REG_OFFSET,
                 {{ADC_CTRL_ADC_EN_CTL_ONESHOT_MODE_BIT, true},
                  {ADC_CTRL_ADC_EN_CTL_ADC_ENABLE_BIT, false}});
  EXPECT_DIF_OK(dif_adc_ctrl_set_enabled(&adc_ctrl_, kDifToggleDisabled));
}

class GetEnabledTest : public AdcCtrlTest {};

TEST_F(GetEnabledTest, NullArgs) {
  dif_toggle_t is_enabled;
  EXPECT_DIF_BADARG(dif_adc_ctrl_get_enabled(nullptr, &is_enabled));
  EXPECT_DIF_BADARG(dif_adc_ctrl_get_enabled(&adc_ctrl_, nullptr));
}

TEST_F(GetEnabledTest, Success) {
  dif_toggle_t is_enabled;

  EXPECT_READ32(ADC_CTRL_ADC_EN_CTL_REG_OFFSET,
                {{ADC_CTRL_ADC_EN_CTL_ADC_ENABLE_BIT, true}});
  EXPECT_DIF_OK(dif_adc_ctrl_get_enabled(&adc_ctrl_, &is_enabled));
  EXPECT_EQ(is_enabled, kDifToggleEnabled);

  EXPECT_READ32(ADC_CTRL_ADC_EN_CTL_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_adc_ctrl_get_enabled(&adc_ctrl_, &is_enabled));
  EXPECT_EQ(is_enabled, kDifToggleDisabled);
}

class SetFilterEnabledTest : public AdcCtrlTest {};

TEST_F(SetFilterEnabledTest, NullHandle) {
  EXPECT_DIF_BADARG(dif_adc_ctrl_filter_set_enabled(
      nullptr, kDifAdcCtrlChannel0, kDifAdcCtrlFilter3, kDifToggleEnabled));
}

TEST_F(SetFilterEnabledTest, BadChannel) {
  EXPECT_DIF_BADARG(dif_adc_ctrl_filter_set_enabled(
      &adc_ctrl_, static_cast<dif_adc_ctrl_channel_t>(2), kDifAdcCtrlFilter3,
      kDifToggleEnabled));
}

TEST_F(SetFilterEnabledTest, BadFilter) {
  EXPECT_DIF_BADARG(dif_adc_ctrl_filter_set_enabled(
      &adc_ctrl_, kDifAdcCtrlChannel0,
      static_cast<dif_adc_ctrl_filter_t>(ADC_CTRL_PARAM_NUM_ADC_FILTER),
      kDifToggleEnabled));
  EXPECT_DIF_BADARG(dif_adc_ctrl_filter_set_enabled(
      &adc_ctrl_, kDifAdcCtrlChannel1,
      static_cast<dif_adc_ctrl_filter_t>(ADC_CTRL_PARAM_NUM_ADC_FILTER),
      kDifToggleEnabled));
}

TEST_F(SetFilterEnabledTest, BadEnabled) {
  EXPECT_DIF_BADARG(dif_adc_ctrl_filter_set_enabled(
      &adc_ctrl_, kDifAdcCtrlChannel0, kDifAdcCtrlFilter3,
      static_cast<dif_toggle_t>(2)));
}

TEST_F(SetFilterEnabledTest, Success) {
  EXPECT_READ32(ADC_CTRL_ADC_CHN1_FILTER_CTL_2_REG_OFFSET,
                {{ADC_CTRL_ADC_CHN1_FILTER_CTL_2_MIN_V_2_OFFSET,
                  filter_config_.min_voltage},
                 {ADC_CTRL_ADC_CHN1_FILTER_CTL_2_MAX_V_2_OFFSET,
                  filter_config_.max_voltage},
                 {ADC_CTRL_ADC_CHN1_FILTER_CTL_2_COND_2_BIT, true},
                 {ADC_CTRL_ADC_CHN1_FILTER_CTL_2_EN_2_BIT, false}});
  EXPECT_WRITE32(ADC_CTRL_ADC_CHN1_FILTER_CTL_2_REG_OFFSET,
                 {{ADC_CTRL_ADC_CHN1_FILTER_CTL_2_MIN_V_2_OFFSET,
                   filter_config_.min_voltage},
                  {ADC_CTRL_ADC_CHN1_FILTER_CTL_2_MAX_V_2_OFFSET,
                   filter_config_.max_voltage},
                  {ADC_CTRL_ADC_CHN1_FILTER_CTL_2_COND_2_BIT, true},
                  {ADC_CTRL_ADC_CHN1_FILTER_CTL_2_EN_2_BIT, true}});
  EXPECT_DIF_OK(dif_adc_ctrl_filter_set_enabled(
      &adc_ctrl_, kDifAdcCtrlChannel1, kDifAdcCtrlFilter2, kDifToggleEnabled));

  EXPECT_READ32(ADC_CTRL_ADC_CHN0_FILTER_CTL_7_REG_OFFSET,
                {{ADC_CTRL_ADC_CHN0_FILTER_CTL_7_MIN_V_7_OFFSET,
                  filter_config_.min_voltage},
                 {ADC_CTRL_ADC_CHN0_FILTER_CTL_7_MAX_V_7_OFFSET,
                  filter_config_.max_voltage},
                 {ADC_CTRL_ADC_CHN0_FILTER_CTL_7_COND_7_BIT, true},
                 {ADC_CTRL_ADC_CHN0_FILTER_CTL_7_EN_7_BIT, true}});
  EXPECT_WRITE32(ADC_CTRL_ADC_CHN0_FILTER_CTL_7_REG_OFFSET,
                 {{ADC_CTRL_ADC_CHN0_FILTER_CTL_7_MIN_V_7_OFFSET,
                   filter_config_.min_voltage},
                  {ADC_CTRL_ADC_CHN0_FILTER_CTL_7_MAX_V_7_OFFSET,
                   filter_config_.max_voltage},
                  {ADC_CTRL_ADC_CHN0_FILTER_CTL_7_COND_7_BIT, true},
                  {ADC_CTRL_ADC_CHN0_FILTER_CTL_7_EN_7_BIT, false}});
  EXPECT_DIF_OK(dif_adc_ctrl_filter_set_enabled(
      &adc_ctrl_, kDifAdcCtrlChannel0, kDifAdcCtrlFilter7, kDifToggleDisabled));
}

class GetFilterEnabledTest : public AdcCtrlTest {};

TEST_F(GetFilterEnabledTest, NullArgs) {
  dif_toggle_t is_enabled;
  EXPECT_DIF_BADARG(dif_adc_ctrl_filter_get_enabled(
      nullptr, kDifAdcCtrlChannel0, kDifAdcCtrlFilter3, &is_enabled));
  EXPECT_DIF_BADARG(dif_adc_ctrl_filter_get_enabled(
      &adc_ctrl_, kDifAdcCtrlChannel0, kDifAdcCtrlFilter3, nullptr));
}

TEST_F(GetFilterEnabledTest, BadChannel) {
  dif_toggle_t is_enabled;
  EXPECT_DIF_BADARG(dif_adc_ctrl_filter_get_enabled(
      &adc_ctrl_, static_cast<dif_adc_ctrl_channel_t>(2), kDifAdcCtrlFilter3,
      &is_enabled));
}

TEST_F(GetFilterEnabledTest, BadFilter) {
  dif_toggle_t is_enabled;
  EXPECT_DIF_BADARG(dif_adc_ctrl_filter_get_enabled(
      &adc_ctrl_, kDifAdcCtrlChannel0,
      static_cast<dif_adc_ctrl_filter_t>(ADC_CTRL_PARAM_NUM_ADC_FILTER),
      &is_enabled));
  EXPECT_DIF_BADARG(dif_adc_ctrl_filter_get_enabled(
      &adc_ctrl_, kDifAdcCtrlChannel1,
      static_cast<dif_adc_ctrl_filter_t>(ADC_CTRL_PARAM_NUM_ADC_FILTER),
      &is_enabled));
}

TEST_F(GetFilterEnabledTest, Success) {
  dif_toggle_t is_enabled;

  EXPECT_READ32(ADC_CTRL_ADC_CHN0_FILTER_CTL_7_REG_OFFSET,
                {{ADC_CTRL_ADC_CHN0_FILTER_CTL_7_EN_7_BIT, true}});
  EXPECT_DIF_OK(dif_adc_ctrl_filter_get_enabled(
      &adc_ctrl_, kDifAdcCtrlChannel0, kDifAdcCtrlFilter7, &is_enabled));
  EXPECT_EQ(is_enabled, kDifToggleEnabled);

  EXPECT_READ32(ADC_CTRL_ADC_CHN1_FILTER_CTL_4_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_adc_ctrl_filter_get_enabled(
      &adc_ctrl_, kDifAdcCtrlChannel1, kDifAdcCtrlFilter4, &is_enabled));
  EXPECT_EQ(is_enabled, kDifToggleDisabled);
}

class GetTriggeredValueTest : public AdcCtrlTest {};

TEST_F(GetTriggeredValueTest, NullArgs) {
  uint16_t value;
  EXPECT_DIF_BADARG(
      dif_adc_ctrl_get_triggered_value(nullptr, kDifAdcCtrlChannel0, &value));
  EXPECT_DIF_BADARG(dif_adc_ctrl_get_triggered_value(
      &adc_ctrl_, kDifAdcCtrlChannel0, nullptr));
}

TEST_F(GetTriggeredValueTest, BadChannel) {
  uint16_t value;
  EXPECT_DIF_BADARG(dif_adc_ctrl_get_triggered_value(
      &adc_ctrl_,
      static_cast<dif_adc_ctrl_channel_t>(ADC_CTRL_PARAM_NUM_ADC_CHANNEL),
      &value));
}

TEST_F(GetTriggeredValueTest, Success) {
  uint16_t value;
  EXPECT_READ32(ADC_CTRL_ADC_CHN_VAL_0_REG_OFFSET,
                {{ADC_CTRL_ADC_CHN_VAL_0_ADC_CHN_VALUE_INTR_0_OFFSET, 1023}});
  EXPECT_DIF_OK(dif_adc_ctrl_get_triggered_value(&adc_ctrl_,
                                                 kDifAdcCtrlChannel0, &value));
  EXPECT_EQ(value, 1023);
}

class GetLatestValueTest : public AdcCtrlTest {};

TEST_F(GetLatestValueTest, NullArgs) {
  uint16_t value;
  EXPECT_DIF_BADARG(
      dif_adc_ctrl_get_latest_value(nullptr, kDifAdcCtrlChannel0, &value));
  EXPECT_DIF_BADARG(
      dif_adc_ctrl_get_latest_value(&adc_ctrl_, kDifAdcCtrlChannel0, nullptr));
}

TEST_F(GetLatestValueTest, BadChannel) {
  uint16_t value;
  EXPECT_DIF_BADARG(dif_adc_ctrl_get_latest_value(
      &adc_ctrl_,
      static_cast<dif_adc_ctrl_channel_t>(ADC_CTRL_PARAM_NUM_ADC_CHANNEL),
      &value));
}

TEST_F(GetLatestValueTest, Success) {
  uint16_t value;
  EXPECT_READ32(ADC_CTRL_ADC_CHN_VAL_0_REG_OFFSET,
                {{ADC_CTRL_ADC_CHN_VAL_0_ADC_CHN_VALUE_0_OFFSET, 1023}});
  EXPECT_DIF_OK(
      dif_adc_ctrl_get_latest_value(&adc_ctrl_, kDifAdcCtrlChannel0, &value));
  EXPECT_EQ(value, 1023);
}

class ResetFsmTest : public AdcCtrlTest {};

TEST_F(ResetFsmTest, NullHandle) {
  EXPECT_DIF_BADARG(dif_adc_ctrl_reset(nullptr));
}

TEST_F(ResetFsmTest, Success) {
  EXPECT_WRITE32(ADC_CTRL_ADC_FSM_RST_REG_OFFSET, 1);
  EXPECT_WRITE32(ADC_CTRL_ADC_FSM_RST_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_adc_ctrl_reset(&adc_ctrl_));
}

class IrqGetCausesTest : public AdcCtrlTest {};

TEST_F(IrqGetCausesTest, NullArgs) {
  uint32_t causes;
  EXPECT_DIF_BADARG(dif_adc_ctrl_irq_get_causes(nullptr, &causes));
  EXPECT_DIF_BADARG(dif_adc_ctrl_irq_get_causes(&adc_ctrl_, nullptr));
}

TEST_F(IrqGetCausesTest, Success) {
  uint32_t causes;
  EXPECT_READ32(ADC_CTRL_ADC_INTR_STATUS_REG_OFFSET, 0x1FF);
  EXPECT_DIF_OK(dif_adc_ctrl_irq_get_causes(&adc_ctrl_, &causes));
  EXPECT_EQ(causes, 0x1FF);
}

class IrqClearCausesTest : public AdcCtrlTest {};

TEST_F(IrqClearCausesTest, NullHandle) {
  EXPECT_DIF_BADARG(
      dif_adc_ctrl_irq_clear_causes(nullptr, kDifAdcCtrlIrqCauseOneshot));
}

TEST_F(IrqClearCausesTest, BadCauses) {
  EXPECT_DIF_BADARG(dif_adc_ctrl_irq_clear_causes(
      &adc_ctrl_, 1U << (ADC_CTRL_PARAM_NUM_ADC_FILTER + 1)));
}

TEST_F(IrqClearCausesTest, Success) {
  EXPECT_WRITE32(ADC_CTRL_FILTER_STATUS_REG_OFFSET, 0x9);
  EXPECT_WRITE32(ADC_CTRL_ADC_INTR_STATUS_REG_OFFSET, 0x9);
  EXPECT_DIF_OK(dif_adc_ctrl_irq_clear_causes(
      &adc_ctrl_, kDifAdcCtrlIrqCauseFilter0 | kDifAdcCtrlIrqCauseFilter3));

  EXPECT_WRITE32(ADC_CTRL_FILTER_STATUS_REG_OFFSET, 0x1);
  EXPECT_WRITE32(ADC_CTRL_ADC_INTR_STATUS_REG_OFFSET, 0x101);
  EXPECT_DIF_OK(dif_adc_ctrl_irq_clear_causes(
      &adc_ctrl_, kDifAdcCtrlIrqCauseFilter0 | kDifAdcCtrlIrqCauseOneshot));
}

class FilterMatchWakeupSetEnabledTest : public AdcCtrlTest {};

TEST_F(FilterMatchWakeupSetEnabledTest, NullHandle) {
  EXPECT_DIF_BADARG(dif_adc_ctrl_filter_match_wakeup_set_enabled(
      nullptr, kDifAdcCtrlFilter3, kDifToggleEnabled));
}

TEST_F(FilterMatchWakeupSetEnabledTest, BadFilter) {
  EXPECT_DIF_BADARG(dif_adc_ctrl_filter_match_wakeup_set_enabled(
      &adc_ctrl_,
      static_cast<dif_adc_ctrl_filter_t>(ADC_CTRL_PARAM_NUM_ADC_FILTER),
      kDifToggleEnabled));
}

TEST_F(FilterMatchWakeupSetEnabledTest, BadEnabled) {
  EXPECT_DIF_BADARG(dif_adc_ctrl_filter_match_wakeup_set_enabled(
      &adc_ctrl_, kDifAdcCtrlFilter7, static_cast<dif_toggle_t>(2)));
}

TEST_F(FilterMatchWakeupSetEnabledTest, Success) {
  EXPECT_READ32(ADC_CTRL_ADC_WAKEUP_CTL_REG_OFFSET, 0xF);
  EXPECT_WRITE32(ADC_CTRL_ADC_WAKEUP_CTL_REG_OFFSET, 0x8F);
  EXPECT_DIF_OK(dif_adc_ctrl_filter_match_wakeup_set_enabled(
      &adc_ctrl_, kDifAdcCtrlFilter7, kDifToggleEnabled));

  EXPECT_READ32(ADC_CTRL_ADC_WAKEUP_CTL_REG_OFFSET, 0x8F);
  EXPECT_WRITE32(ADC_CTRL_ADC_WAKEUP_CTL_REG_OFFSET, 0xF);
  EXPECT_DIF_OK(dif_adc_ctrl_filter_match_wakeup_set_enabled(
      &adc_ctrl_, kDifAdcCtrlFilter7, kDifToggleDisabled));
}

class FilterMatchWakeupGetEnabledTest : public AdcCtrlTest {};

TEST_F(FilterMatchWakeupGetEnabledTest, NullArgs) {
  dif_toggle_t is_enabled;
  EXPECT_DIF_BADARG(dif_adc_ctrl_filter_match_wakeup_get_enabled(
      nullptr, kDifAdcCtrlFilter3, &is_enabled));
  EXPECT_DIF_BADARG(dif_adc_ctrl_filter_match_wakeup_get_enabled(
      &adc_ctrl_, kDifAdcCtrlFilter3, nullptr));
}

TEST_F(FilterMatchWakeupGetEnabledTest, BadFilter) {
  dif_toggle_t is_enabled;
  EXPECT_DIF_BADARG(dif_adc_ctrl_filter_match_wakeup_get_enabled(
      &adc_ctrl_,
      static_cast<dif_adc_ctrl_filter_t>(ADC_CTRL_PARAM_NUM_ADC_FILTER),
      &is_enabled));
}

TEST_F(FilterMatchWakeupGetEnabledTest, Success) {
  dif_toggle_t is_enabled;

  EXPECT_READ32(ADC_CTRL_ADC_WAKEUP_CTL_REG_OFFSET, 0x88);
  EXPECT_DIF_OK(dif_adc_ctrl_filter_match_wakeup_get_enabled(
      &adc_ctrl_, kDifAdcCtrlFilter3, &is_enabled));
  EXPECT_EQ(is_enabled, kDifToggleEnabled);

  EXPECT_READ32(ADC_CTRL_ADC_WAKEUP_CTL_REG_OFFSET, 0x88);
  EXPECT_DIF_OK(dif_adc_ctrl_filter_match_wakeup_get_enabled(
      &adc_ctrl_, kDifAdcCtrlFilter2, &is_enabled));
  EXPECT_EQ(is_enabled, kDifToggleDisabled);
}

class IrqCauseSetEnabledTest : public AdcCtrlTest {};

TEST_F(IrqCauseSetEnabledTest, NullHandle) {
  EXPECT_DIF_BADARG(dif_adc_ctrl_irq_cause_set_enabled(
      nullptr, kDifAdcCtrlIrqCauseFilter2, kDifToggleEnabled));
}

TEST_F(IrqCauseSetEnabledTest, BadCauses) {
  EXPECT_DIF_BADARG(dif_adc_ctrl_irq_cause_set_enabled(
      &adc_ctrl_, kDifAdcCtrlIrqCauseAll + 1, kDifToggleEnabled));
}

TEST_F(IrqCauseSetEnabledTest, BadEnabled) {
  EXPECT_DIF_BADARG(dif_adc_ctrl_irq_cause_set_enabled(
      &adc_ctrl_, kDifAdcCtrlIrqCauseAll, static_cast<dif_toggle_t>(2)));
}

TEST_F(IrqCauseSetEnabledTest, Success) {
  EXPECT_READ32(ADC_CTRL_ADC_INTR_CTL_REG_OFFSET, 0x33);
  EXPECT_WRITE32(ADC_CTRL_ADC_INTR_CTL_REG_OFFSET, 0x3F);
  EXPECT_DIF_OK(dif_adc_ctrl_irq_cause_set_enabled(
      &adc_ctrl_, kDifAdcCtrlIrqCauseFilter2 | kDifAdcCtrlIrqCauseFilter3,
      kDifToggleEnabled));

  EXPECT_READ32(ADC_CTRL_ADC_INTR_CTL_REG_OFFSET, 0x3F);
  EXPECT_WRITE32(ADC_CTRL_ADC_INTR_CTL_REG_OFFSET, 0x33);
  EXPECT_DIF_OK(dif_adc_ctrl_irq_cause_set_enabled(
      &adc_ctrl_, kDifAdcCtrlIrqCauseFilter2 | kDifAdcCtrlIrqCauseFilter3,
      kDifToggleDisabled));
}

class IrqCauseGetEnabledTest : public AdcCtrlTest {};

TEST_F(IrqCauseGetEnabledTest, NullArgs) {
  uint32_t enabled_causes;
  EXPECT_DIF_BADARG(
      dif_adc_ctrl_irq_cause_get_enabled(nullptr, &enabled_causes));
  EXPECT_DIF_BADARG(dif_adc_ctrl_irq_cause_get_enabled(&adc_ctrl_, nullptr));
}

TEST_F(IrqCauseGetEnabledTest, Success) {
  uint32_t enabled_causes;
  EXPECT_READ32(ADC_CTRL_ADC_INTR_CTL_REG_OFFSET, 0x1AA);
  EXPECT_DIF_OK(
      dif_adc_ctrl_irq_cause_get_enabled(&adc_ctrl_, &enabled_causes));
  EXPECT_EQ(enabled_causes, 0x1AA);
}

}  // namespace
}  // namespace dif_adc_ctrl_unittest
