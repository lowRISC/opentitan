// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_pwm.h"

#include <cstring>
#include <limits>
#include <ostream>

#include "gtest/gtest.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/testing/mock_mmio.h"

#include "pwm_regs.h"  // Generated.

namespace dif_pwm_unittest {
namespace {
using ::mock_mmio::LeInt;
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;

class PwmTest : public testing::Test, public MmioTest {
 protected:
  dif_pwm_t pwm_ = {.base_addr = dev().region()};
  dif_pwm_config_t config_ = {
      .clock_divisor = 2,
      .beats_per_pulse_cycle = 64,
  };
  dif_pwm_channel_config_t channel_config_ = {
      .duty_cycle_a = 22,
      .duty_cycle_b = 44,
      .phase_delay = 0,
      .mode = kDifPwmModeFirmware,
      .polarity = kDifPwmPolarityActiveHigh,
      .blink_parameter_x = 10,
      .blink_parameter_y = 8,
  };
  uint32_t duty_cycle_resolution_ =
      30 - bitfield_count_leading_zeroes32(config_.beats_per_pulse_cycle);
  uint32_t phase_cntr_ticks_per_beat_ =
      (1U << (16 - duty_cycle_resolution_ - 1));
};

class ConfigTest : public PwmTest {};

TEST_F(ConfigTest, NullArgs) {
  EXPECT_EQ(dif_pwm_configure(nullptr, config_), kDifBadArg);
}

TEST_F(ConfigTest, BadArgs) {
  // Bad clock divisor.
  config_.clock_divisor = PWM_CFG_CLK_DIV_MASK + 1;
  config_.beats_per_pulse_cycle = 2;
  EXPECT_EQ(dif_pwm_configure(&pwm_, config_), kDifBadArg);

  // Bad duty cycle resolution.
  config_.clock_divisor = 2;
  config_.beats_per_pulse_cycle = (1U << (PWM_CFG_DC_RESN_MASK + 1)) + 1;
  EXPECT_EQ(dif_pwm_configure(&pwm_, config_), kDifBadArg);

  // Bad duty cycle resolution.
  config_.clock_divisor = 2;
  config_.beats_per_pulse_cycle = 1;
  EXPECT_EQ(dif_pwm_configure(&pwm_, config_), kDifBadArg);
}

TEST_F(ConfigTest, Locked) {
  EXPECT_READ32(PWM_REGWEN_REG_OFFSET, 0);
  EXPECT_EQ(dif_pwm_configure(&pwm_, config_), kDifLocked);
}

TEST_F(ConfigTest, Success) {
  EXPECT_READ32(PWM_REGWEN_REG_OFFSET, 1);
  EXPECT_READ32(PWM_CFG_REG_OFFSET, 1U << 31);
  EXPECT_WRITE32(PWM_CFG_REG_OFFSET, 0);
  EXPECT_WRITE32(PWM_CFG_REG_OFFSET, {{PWM_CFG_CLK_DIV_OFFSET, 2},
                                      {PWM_CFG_DC_RESN_OFFSET, 5},
                                      {PWM_CFG_CNTR_EN_BIT, 1}})
  EXPECT_EQ(dif_pwm_configure(&pwm_, config_), kDifOk);
}

class ConfigChannelTest : public PwmTest {};

TEST_F(ConfigChannelTest, NullArgs) {
  EXPECT_EQ(
      dif_pwm_configure_channel(nullptr, kDifPwmChannel0, channel_config_),
      kDifBadArg);
}

TEST_F(ConfigChannelTest, Locked) {
  EXPECT_READ32(PWM_REGWEN_REG_OFFSET, 0);
  EXPECT_EQ(dif_pwm_configure_channel(&pwm_, kDifPwmChannel0, channel_config_),
            kDifLocked);
}

TEST_F(ConfigChannelTest, BadChannel) {
  EXPECT_READ32(PWM_REGWEN_REG_OFFSET, 1);
  EXPECT_READ32(PWM_CFG_REG_OFFSET,
                {{PWM_CFG_DC_RESN_OFFSET, duty_cycle_resolution_}});
  EXPECT_READ32(PWM_INVERT_REG_OFFSET, 0);
  EXPECT_EQ(dif_pwm_configure_channel(
                &pwm_,
                static_cast<dif_pwm_channel_t>(1U << (PWM_PARAM_N_OUTPUTS + 1)),
                channel_config_),
            kDifBadArg);

  // Channel enums should be one-hot encoded.
  EXPECT_READ32(PWM_REGWEN_REG_OFFSET, 1);
  EXPECT_READ32(PWM_CFG_REG_OFFSET,
                {{PWM_CFG_DC_RESN_OFFSET, duty_cycle_resolution_}});
  EXPECT_READ32(PWM_INVERT_REG_OFFSET, 0);
  EXPECT_EQ(dif_pwm_configure_channel(&pwm_, static_cast<dif_pwm_channel_t>(3),
                                      channel_config_),
            kDifBadArg);
}

TEST_F(ConfigChannelTest, BadDutyCycle) {
  EXPECT_READ32(PWM_REGWEN_REG_OFFSET, 1);
  EXPECT_READ32(PWM_CFG_REG_OFFSET,
                {{PWM_CFG_DC_RESN_OFFSET, duty_cycle_resolution_}});

  channel_config_.duty_cycle_a = config_.beats_per_pulse_cycle;
  EXPECT_EQ(dif_pwm_configure_channel(&pwm_, kDifPwmChannel0, channel_config_),
            kDifBadArg);

  EXPECT_READ32(PWM_REGWEN_REG_OFFSET, 1);
  EXPECT_READ32(PWM_CFG_REG_OFFSET,
                {{PWM_CFG_DC_RESN_OFFSET, duty_cycle_resolution_}});
  channel_config_.duty_cycle_a = 24;
  channel_config_.duty_cycle_b = config_.beats_per_pulse_cycle;
  EXPECT_EQ(dif_pwm_configure_channel(&pwm_, kDifPwmChannel0, channel_config_),
            kDifBadArg);
}

TEST_F(ConfigChannelTest, BadPhaseDelay) {
  EXPECT_READ32(PWM_REGWEN_REG_OFFSET, 1);
  EXPECT_READ32(PWM_CFG_REG_OFFSET,
                {{PWM_CFG_DC_RESN_OFFSET, duty_cycle_resolution_}});

  channel_config_.phase_delay = config_.beats_per_pulse_cycle;
  EXPECT_EQ(dif_pwm_configure_channel(&pwm_, kDifPwmChannel0, channel_config_),
            kDifBadArg);
}

TEST_F(ConfigChannelTest, BadMode) {
  EXPECT_READ32(PWM_REGWEN_REG_OFFSET, 1);
  EXPECT_READ32(PWM_CFG_REG_OFFSET,
                {{PWM_CFG_DC_RESN_OFFSET, duty_cycle_resolution_}});
  EXPECT_READ32(PWM_INVERT_REG_OFFSET, 0);

  channel_config_.mode = static_cast<dif_pwm_mode_t>(3);
  EXPECT_EQ(dif_pwm_configure_channel(&pwm_, kDifPwmChannel0, channel_config_),
            kDifBadArg);
}

TEST_F(ConfigChannelTest, BadPolarity) {
  channel_config_.polarity = static_cast<dif_pwm_polarity_t>(3);
  EXPECT_EQ(dif_pwm_configure_channel(&pwm_, kDifPwmChannel0, channel_config_),
            kDifBadArg);
}

TEST_F(ConfigChannelTest, BadBlinkParameterX) {
  EXPECT_READ32(PWM_REGWEN_REG_OFFSET, 1);
  EXPECT_READ32(PWM_CFG_REG_OFFSET,
                {{PWM_CFG_DC_RESN_OFFSET, duty_cycle_resolution_}});
  EXPECT_READ32(PWM_INVERT_REG_OFFSET, 0);

  channel_config_.mode = kDifPwmModeHeartbeat;
  channel_config_.blink_parameter_y = config_.beats_per_pulse_cycle;
  EXPECT_EQ(dif_pwm_configure_channel(&pwm_, kDifPwmChannel0, channel_config_),
            kDifBadArg);
}

TEST_F(ConfigChannelTest, FirmwareModeSuccess) {
  EXPECT_READ32(PWM_REGWEN_REG_OFFSET, 1);
  EXPECT_READ32(PWM_CFG_REG_OFFSET,
                {{PWM_CFG_DC_RESN_OFFSET, duty_cycle_resolution_}});
  EXPECT_READ32(PWM_INVERT_REG_OFFSET, 0);
  EXPECT_WRITE32(PWM_DUTY_CYCLE_0_REG_OFFSET,
                 {{PWM_DUTY_CYCLE_0_A_0_OFFSET,
                   channel_config_.duty_cycle_a * phase_cntr_ticks_per_beat_},
                  {PWM_DUTY_CYCLE_0_B_0_OFFSET,
                   channel_config_.duty_cycle_b * phase_cntr_ticks_per_beat_}});
  EXPECT_WRITE32(PWM_PWM_PARAM_0_REG_OFFSET,
                 {{PWM_PWM_PARAM_0_PHASE_DELAY_0_OFFSET,
                   channel_config_.phase_delay * phase_cntr_ticks_per_beat_},
                  {PWM_PWM_PARAM_0_HTBT_EN_0_BIT, 0},
                  {PWM_PWM_PARAM_0_BLINK_EN_0_BIT, 0}});
  EXPECT_WRITE32(PWM_INVERT_REG_OFFSET, 0);

  EXPECT_EQ(dif_pwm_configure_channel(&pwm_, kDifPwmChannel0, channel_config_),
            kDifOk);
}

TEST_F(ConfigChannelTest, BlinkModeSuccess) {
  EXPECT_READ32(PWM_REGWEN_REG_OFFSET, 1);
  EXPECT_READ32(PWM_CFG_REG_OFFSET,
                {{PWM_CFG_DC_RESN_OFFSET, duty_cycle_resolution_}});
  EXPECT_READ32(PWM_INVERT_REG_OFFSET, 0);
  EXPECT_WRITE32(PWM_DUTY_CYCLE_0_REG_OFFSET,
                 {{PWM_DUTY_CYCLE_0_A_0_OFFSET,
                   channel_config_.duty_cycle_a * phase_cntr_ticks_per_beat_},
                  {PWM_DUTY_CYCLE_0_B_0_OFFSET,
                   channel_config_.duty_cycle_b * phase_cntr_ticks_per_beat_}});
  EXPECT_WRITE32(PWM_PWM_PARAM_0_REG_OFFSET,
                 {{PWM_PWM_PARAM_0_PHASE_DELAY_0_OFFSET,
                   channel_config_.phase_delay * phase_cntr_ticks_per_beat_},
                  {PWM_PWM_PARAM_0_HTBT_EN_0_BIT, 0},
                  {PWM_PWM_PARAM_0_BLINK_EN_0_BIT, 1}});
  EXPECT_WRITE32(
      PWM_BLINK_PARAM_0_REG_OFFSET,
      {{PWM_BLINK_PARAM_0_Y_0_OFFSET, channel_config_.blink_parameter_y},
       {PWM_BLINK_PARAM_0_X_0_OFFSET, channel_config_.blink_parameter_x}});
  EXPECT_WRITE32(PWM_INVERT_REG_OFFSET, 0);

  channel_config_.mode = kDifPwmModeBlink;
  EXPECT_EQ(dif_pwm_configure_channel(&pwm_, kDifPwmChannel0, channel_config_),
            kDifOk);
}

TEST_F(ConfigChannelTest, HeartbeatModeSuccess) {
  EXPECT_READ32(PWM_REGWEN_REG_OFFSET, 1);
  EXPECT_READ32(PWM_CFG_REG_OFFSET,
                {{PWM_CFG_DC_RESN_OFFSET, duty_cycle_resolution_}});
  EXPECT_READ32(PWM_INVERT_REG_OFFSET, 0);
  EXPECT_WRITE32(PWM_DUTY_CYCLE_0_REG_OFFSET,
                 {{PWM_DUTY_CYCLE_0_A_0_OFFSET,
                   channel_config_.duty_cycle_a * phase_cntr_ticks_per_beat_},
                  {PWM_DUTY_CYCLE_0_B_0_OFFSET,
                   channel_config_.duty_cycle_b * phase_cntr_ticks_per_beat_}});
  EXPECT_WRITE32(PWM_PWM_PARAM_0_REG_OFFSET,
                 {{PWM_PWM_PARAM_0_PHASE_DELAY_0_OFFSET,
                   channel_config_.phase_delay * phase_cntr_ticks_per_beat_},
                  {PWM_PWM_PARAM_0_HTBT_EN_0_BIT, 1},
                  {PWM_PWM_PARAM_0_BLINK_EN_0_BIT, 0}});
  EXPECT_WRITE32(
      PWM_BLINK_PARAM_0_REG_OFFSET,
      {{PWM_BLINK_PARAM_0_Y_0_OFFSET,
        channel_config_.blink_parameter_y * phase_cntr_ticks_per_beat_},
       {PWM_BLINK_PARAM_0_X_0_OFFSET, channel_config_.blink_parameter_x}});
  EXPECT_WRITE32(PWM_INVERT_REG_OFFSET, 0);

  channel_config_.mode = kDifPwmModeHeartbeat;
  EXPECT_EQ(dif_pwm_configure_channel(&pwm_, kDifPwmChannel0, channel_config_),
            kDifOk);
}

}  // namespace
}  // namespace dif_pwm_unittest
