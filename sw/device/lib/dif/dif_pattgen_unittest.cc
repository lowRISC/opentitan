// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_pattgen.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "pattgen_regs.h"  // Generated.

namespace dif_pattgen_unittest {
namespace {
using ::mock_mmio::LeInt;
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;

class PattgenTest : public testing::Test, public MmioTest {
 protected:
  dif_pattgen_t pattgen_ = {.base_addr = dev().region()};
  dif_pattgen_channel_config_t config_ = {
      .polarity = kDifPattgenPolarityHigh,
      .clock_divisor = 31,
      .seed_pattern_lower_word = 0xDEADBEEF,
      .seed_pattern_upper_word = 0xCAFEFEED,
      .seed_pattern_length = 64,
      .num_pattern_repetitions = 64,
  };
};

class ConfigChannelTest : public PattgenTest {};

TEST_F(ConfigChannelTest, NullHandle) {
  EXPECT_DIF_BADARG(
      dif_pattgen_configure_channel(nullptr, kDifPattgenChannel0, config_));
}

TEST_F(ConfigChannelTest, BadChannel) {
  EXPECT_DIF_BADARG(dif_pattgen_configure_channel(
      &pattgen_, static_cast<dif_pattgen_channel_t>(2), config_));
}

TEST_F(ConfigChannelTest, BadPolarity) {
  config_.polarity = static_cast<dif_pattgen_polarity_t>(2);
  EXPECT_DIF_BADARG(
      dif_pattgen_configure_channel(&pattgen_, kDifPattgenChannel0, config_));
}

TEST_F(ConfigChannelTest, BadSeedPatternLength) {
  config_.seed_pattern_length = 0;
  EXPECT_DIF_BADARG(
      dif_pattgen_configure_channel(&pattgen_, kDifPattgenChannel0, config_));

  config_.seed_pattern_length = 65;
  EXPECT_DIF_BADARG(
      dif_pattgen_configure_channel(&pattgen_, kDifPattgenChannel0, config_));
}

TEST_F(ConfigChannelTest, BadNumPatternRepetitions) {
  config_.num_pattern_repetitions = 0;
  EXPECT_DIF_BADARG(
      dif_pattgen_configure_channel(&pattgen_, kDifPattgenChannel0, config_));

  config_.num_pattern_repetitions = 1025;
  EXPECT_DIF_BADARG(
      dif_pattgen_configure_channel(&pattgen_, kDifPattgenChannel0, config_));
}

TEST_F(ConfigChannelTest, ConfigAttemptWhileEnabled) {
  EXPECT_READ32(PATTGEN_CTRL_REG_OFFSET, {{PATTGEN_CTRL_ENABLE_CH0_BIT, 1}});
  EXPECT_EQ(
      dif_pattgen_configure_channel(&pattgen_, kDifPattgenChannel0, config_),
      kDifError);

  EXPECT_READ32(PATTGEN_CTRL_REG_OFFSET, {{PATTGEN_CTRL_ENABLE_CH1_BIT, 1}});
  EXPECT_EQ(
      dif_pattgen_configure_channel(&pattgen_, kDifPattgenChannel1, config_),
      kDifError);
}

TEST_F(ConfigChannelTest, FullSeedSuccess) {
  EXPECT_READ32(PATTGEN_CTRL_REG_OFFSET, {{PATTGEN_CTRL_ENABLE_CH0_BIT, 0},
                                          {PATTGEN_CTRL_ENABLE_CH1_BIT, 1}});
  EXPECT_WRITE32(PATTGEN_CTRL_REG_OFFSET, {{PATTGEN_CTRL_POLARITY_CH0_BIT, 1},
                                           {PATTGEN_CTRL_ENABLE_CH1_BIT, 1}});
  EXPECT_WRITE32(PATTGEN_PREDIV_CH0_REG_OFFSET, config_.clock_divisor);
  EXPECT_WRITE32(PATTGEN_DATA_CH0_0_REG_OFFSET,
                 config_.seed_pattern_lower_word);
  EXPECT_WRITE32(PATTGEN_DATA_CH0_1_REG_OFFSET,
                 config_.seed_pattern_upper_word);
  EXPECT_READ32(PATTGEN_SIZE_REG_OFFSET, {{PATTGEN_SIZE_REPS_CH1_OFFSET, 127},
                                          {PATTGEN_SIZE_LEN_CH1_OFFSET, 31}});
  EXPECT_WRITE32(PATTGEN_SIZE_REG_OFFSET,
                 {{PATTGEN_SIZE_LEN_CH0_OFFSET,
                   static_cast<uint8_t>(config_.seed_pattern_length - 1)},
                  {PATTGEN_SIZE_REPS_CH0_OFFSET,
                   static_cast<uint16_t>(config_.num_pattern_repetitions - 1)},
                  {PATTGEN_SIZE_LEN_CH1_OFFSET, 31},
                  {PATTGEN_SIZE_REPS_CH1_OFFSET, 127}});
  EXPECT_DIF_OK(
      dif_pattgen_configure_channel(&pattgen_, kDifPattgenChannel0, config_));
}

TEST_F(ConfigChannelTest, HalfSeedSuccess) {
  config_.seed_pattern_length = 16;
  EXPECT_READ32(PATTGEN_CTRL_REG_OFFSET, {{PATTGEN_CTRL_ENABLE_CH1_BIT, 0}});
  EXPECT_WRITE32(PATTGEN_CTRL_REG_OFFSET, {{PATTGEN_CTRL_POLARITY_CH1_BIT, 1}});
  EXPECT_WRITE32(PATTGEN_PREDIV_CH1_REG_OFFSET, config_.clock_divisor);
  EXPECT_WRITE32(PATTGEN_DATA_CH1_0_REG_OFFSET,
                 config_.seed_pattern_lower_word);
  EXPECT_READ32(PATTGEN_SIZE_REG_OFFSET, 0);
  EXPECT_WRITE32(
      PATTGEN_SIZE_REG_OFFSET,
      {{PATTGEN_SIZE_LEN_CH1_OFFSET,
        static_cast<uint8_t>(config_.seed_pattern_length - 1)},
       {PATTGEN_SIZE_REPS_CH1_OFFSET,
        static_cast<uint16_t>(config_.num_pattern_repetitions - 1)}});
  EXPECT_DIF_OK(
      dif_pattgen_configure_channel(&pattgen_, kDifPattgenChannel1, config_));
}

class ChannelSetEnabledTest : public PattgenTest {};

TEST_F(ChannelSetEnabledTest, NullHandle) {
  EXPECT_DIF_BADARG(dif_pattgen_channel_set_enabled(
      nullptr, kDifPattgenChannel0, kDifToggleEnabled));
}

TEST_F(ChannelSetEnabledTest, BadChannel) {
  EXPECT_DIF_BADARG(dif_pattgen_channel_set_enabled(
      &pattgen_, static_cast<dif_pattgen_channel_t>(2), kDifToggleEnabled));
}

TEST_F(ChannelSetEnabledTest, BadEnableValue) {
  EXPECT_DIF_BADARG(dif_pattgen_channel_set_enabled(
      &pattgen_, kDifPattgenChannel0, static_cast<dif_toggle_t>(2)));
}

TEST_F(ChannelSetEnabledTest, Success) {
  EXPECT_READ32(PATTGEN_CTRL_REG_OFFSET, {{PATTGEN_CTRL_ENABLE_CH0_BIT, 0},
                                          {PATTGEN_CTRL_ENABLE_CH1_BIT, 1}});
  EXPECT_WRITE32(PATTGEN_CTRL_REG_OFFSET, {{PATTGEN_CTRL_ENABLE_CH0_BIT, 1},
                                           {PATTGEN_CTRL_ENABLE_CH1_BIT, 1}});
  EXPECT_DIF_OK(dif_pattgen_channel_set_enabled(&pattgen_, kDifPattgenChannel0,
                                                kDifToggleEnabled));

  EXPECT_READ32(PATTGEN_CTRL_REG_OFFSET, {{PATTGEN_CTRL_ENABLE_CH0_BIT, 1},
                                          {PATTGEN_CTRL_ENABLE_CH1_BIT, 1}});
  EXPECT_WRITE32(PATTGEN_CTRL_REG_OFFSET, {{PATTGEN_CTRL_ENABLE_CH0_BIT, 1},
                                           {PATTGEN_CTRL_ENABLE_CH1_BIT, 0}});
  EXPECT_DIF_OK(dif_pattgen_channel_set_enabled(&pattgen_, kDifPattgenChannel1,
                                                kDifToggleDisabled));
}

class ChannelGetEnabledTest : public PattgenTest {};

TEST_F(ChannelGetEnabledTest, NullArgs) {
  dif_toggle_t is_enabled;
  EXPECT_DIF_BADARG(dif_pattgen_channel_get_enabled(
      nullptr, kDifPattgenChannel0, &is_enabled));
  EXPECT_DIF_BADARG(
      dif_pattgen_channel_get_enabled(&pattgen_, kDifPattgenChannel0, nullptr));
}

TEST_F(ChannelGetEnabledTest, BadChannel) {
  dif_toggle_t is_enabled;
  EXPECT_DIF_BADARG(dif_pattgen_channel_get_enabled(
      &pattgen_, static_cast<dif_pattgen_channel_t>(2), &is_enabled));
}

TEST_F(ChannelGetEnabledTest, Success) {
  dif_toggle_t is_enabled;

  EXPECT_READ32(PATTGEN_CTRL_REG_OFFSET, {{PATTGEN_CTRL_ENABLE_CH1_BIT, 1}});
  EXPECT_DIF_OK(dif_pattgen_channel_get_enabled(&pattgen_, kDifPattgenChannel1,
                                                &is_enabled));
  EXPECT_EQ(is_enabled, kDifToggleEnabled);

  EXPECT_READ32(PATTGEN_CTRL_REG_OFFSET, {{PATTGEN_CTRL_ENABLE_CH0_BIT, 0}});
  EXPECT_DIF_OK(dif_pattgen_channel_get_enabled(&pattgen_, kDifPattgenChannel0,
                                                &is_enabled));
  EXPECT_EQ(is_enabled, kDifToggleDisabled);
}

}  // namespace
}  // namespace dif_pattgen_unittest
