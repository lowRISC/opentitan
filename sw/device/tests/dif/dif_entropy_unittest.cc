// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_entropy.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/testing/mock_mmio.h"

#include "entropy_src_regs.h"  // Generated

namespace dif_entropy_unittest {
namespace {

class DifEntropyTest : public testing::Test, public mock_mmio::MmioTest {
 protected:
  const dif_entropy_params_t params_ = {.base_addr = dev().region()};
  const dif_entropy_t entropy_ = {
      .params = {.base_addr = dev().region()},
  };
};

class InitTest : public DifEntropyTest {};

TEST_F(InitTest, BadArgs) {
  EXPECT_EQ(dif_entropy_init(params_, nullptr), kDifEntropyBadArg);
}

TEST_F(InitTest, Init) {
  dif_entropy_t entropy;
  EXPECT_EQ(dif_entropy_init(params_, &entropy), kDifEntropyOk);
}

class ConfigTest : public DifEntropyTest {
 protected:
  dif_entropy_config_t config_ = {
      .mode = kDifEntropyModeLfsr,
      .tests = {0},
      .reset_health_test_registers = false,
      .single_bit_mode = kDifEntropySingleBitModeDisabled,
      .route_to_firmware = false,
      .fips_mode = false,
      .test_config = {0},
      .sample_rate = 64,
      .lfsr_seed = 4,
  };
};

TEST_F(ConfigTest, NullArgs) {
  EXPECT_EQ(dif_entropy_configure(nullptr, {}), kDifEntropyBadArg);
}

TEST_F(ConfigTest, LfsrSeedBadArg) {
  config_.lfsr_seed = 16;
  EXPECT_EQ(dif_entropy_configure(&entropy_, config_), kDifEntropyBadArg);
}

struct ConfigParams {
  dif_entropy_mode_t mode;
  dif_entropy_single_bit_mode_t single_bit_mode;
  bool route_to_firmware;
  bool reset_health_test_registers;

  uint32_t expected_mode;
  bool expected_rng_bit_en;
  uint32_t expected_rng_sel;
  uint32_t expected_seed;
};

class ConfigTestAllParams : public ConfigTest,
                            public testing::WithParamInterface<ConfigParams> {};

TEST_P(ConfigTestAllParams, ValidConfigurationMode) {
  const ConfigParams &test_param = GetParam();
  config_.mode = test_param.mode;
  config_.single_bit_mode = test_param.single_bit_mode;
  config_.route_to_firmware = test_param.route_to_firmware;
  config_.reset_health_test_registers = test_param.reset_health_test_registers;

  EXPECT_WRITE32(ENTROPY_SRC_SEED_REG_OFFSET, test_param.expected_seed);
  EXPECT_WRITE32(ENTROPY_SRC_RATE_REG_OFFSET, 64);
  EXPECT_WRITE32(ENTROPY_SRC_ENTROPY_CONTROL_REG_OFFSET,
                 {
                     {ENTROPY_SRC_ENTROPY_CONTROL_ES_ROUTE_BIT,
                      test_param.route_to_firmware},
                     {ENTROPY_SRC_ENTROPY_CONTROL_ES_TYPE_BIT, false},
                 });
  EXPECT_WRITE32(ENTROPY_SRC_FW_OV_CONTROL_REG_OFFSET, 0);
  EXPECT_WRITE32(
      ENTROPY_SRC_CONF_REG_OFFSET,
      {
          {ENTROPY_SRC_CONF_ENABLE_OFFSET, test_param.expected_mode},
          {ENTROPY_SRC_CONF_BOOT_BYPASS_DISABLE_BIT, true},
          {ENTROPY_SRC_CONF_REPCNT_DISABLE_BIT, true},
          {ENTROPY_SRC_CONF_ADAPTP_DISABLE_BIT, true},
          {ENTROPY_SRC_CONF_BUCKET_DISABLE_BIT, true},
          {ENTROPY_SRC_CONF_MARKOV_DISABLE_BIT, true},
          {ENTROPY_SRC_CONF_HEALTH_TEST_CLR_BIT,
           test_param.reset_health_test_registers},
          {ENTROPY_SRC_CONF_RNG_BIT_EN_BIT, test_param.expected_rng_bit_en},
          {ENTROPY_SRC_CONF_RNG_BIT_SEL_OFFSET, test_param.expected_rng_sel},
          {ENTROPY_SRC_CONF_EXTHT_ENABLE_BIT, false},
      });

  EXPECT_EQ(dif_entropy_configure(&entropy_, config_), kDifEntropyOk);
}

INSTANTIATE_TEST_SUITE_P(
    ConfigTestAllParams, ConfigTestAllParams,
    testing::Values(
        // Test entropy mode.
        ConfigParams{kDifEntropyModeDisabled, kDifEntropySingleBitModeDisabled,
                     false, 0, false, 0, 0},
        ConfigParams{kDifEntropyModePtrng, kDifEntropySingleBitModeDisabled,
                     false, false, 1, false, 0, 0},
        ConfigParams{kDifEntropyModeLfsr, kDifEntropySingleBitModeDisabled,
                     false, false, 2, false, 0, 4},
        // Test route_to_firmware
        ConfigParams{kDifEntropyModeLfsr, kDifEntropySingleBitModeDisabled,
                     true, false, 2, false, 0, 4},
        // Test reset_health_test_registers
        ConfigParams{kDifEntropyModeLfsr, kDifEntropySingleBitModeDisabled,
                     true, true, 2, false, 0, 4},
        // Test single_bit_mode
        ConfigParams{kDifEntropyModeLfsr, kDifEntropySingleBitMode0, true, true,
                     2, true, 0, 4},
        ConfigParams{kDifEntropyModeLfsr, kDifEntropySingleBitMode1, true, true,
                     2, true, 1, 4},
        ConfigParams{kDifEntropyModeLfsr, kDifEntropySingleBitMode2, true, true,
                     2, true, 2, 4},
        ConfigParams{kDifEntropyModeLfsr, kDifEntropySingleBitMode3, true, true,
                     2, true, 3, 4}));

class ReadTest : public DifEntropyTest {};

TEST_F(ReadTest, EntropyBadArg) {
  uint32_t word;
  EXPECT_EQ(dif_entropy_read(nullptr, &word), kDifEntropyBadArg);
}

TEST_F(ReadTest, WordBadArg) {
  EXPECT_EQ(dif_entropy_read(&entropy_, nullptr), kDifEntropyBadArg);
}

TEST_F(ReadTest, ReadOk) {
  const uint32_t expected_word = 0x65585497;
  EXPECT_READ32(ENTROPY_SRC_ENTROPY_DATA_REG_OFFSET, expected_word);

  uint32_t got_word;
  EXPECT_EQ(dif_entropy_read(&entropy_, &got_word), kDifEntropyOk);
  EXPECT_EQ(got_word, expected_word);
}

}  // namespace
}  // namespace dif_entropy_unittest
