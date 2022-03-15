// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_adc_ctrl.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/testing/mock_mmio.h"
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
                   config_.power_up_time_aon_cycles}});
  EXPECT_WRITE32(ADC_CTRL_ADC_LP_SAMPLE_CTL_REG_OFFSET, 0);
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
                   config_.power_up_time_aon_cycles}});
  EXPECT_WRITE32(ADC_CTRL_ADC_LP_SAMPLE_CTL_REG_OFFSET, 0);
  EXPECT_WRITE32(ADC_CTRL_ADC_SAMPLE_CTL_REG_OFFSET, 0);
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
                  {ADC_CTRL_ADC_CHN1_FILTER_CTL_2_COND_2_BIT, true},
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
                  {ADC_CTRL_ADC_CHN0_FILTER_CTL_6_COND_6_BIT, true},
                  {ADC_CTRL_ADC_CHN0_FILTER_CTL_6_EN_6_BIT, true}});
  EXPECT_READ32(ADC_CTRL_ADC_WAKEUP_CTL_REG_OFFSET, 0x4);
  EXPECT_WRITE32(ADC_CTRL_ADC_WAKEUP_CTL_REG_OFFSET, 0x44);
  EXPECT_READ32(ADC_CTRL_ADC_INTR_CTL_REG_OFFSET, 0x4);
  EXPECT_WRITE32(ADC_CTRL_ADC_INTR_CTL_REG_OFFSET, 0x44);
  filter_config_.filter = kDifAdcCtrlFilter6;
  EXPECT_DIF_OK(dif_adc_ctrl_configure_filter(
      &adc_ctrl_, kDifAdcCtrlChannel0, filter_config_, kDifToggleEnabled));
}

}  // namespace
}  // namespace dif_adc_ctrl_unittest
