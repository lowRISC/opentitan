// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_entropy_src.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"
#include "sw/device/lib/dif/dif_base.h"

#include "entropy_src_regs.h"  // Generated

namespace dif_entropy_src_unittest {
namespace {

class DifEntropySrcTest : public testing::Test, public mock_mmio::MmioTest {
 protected:
  const dif_entropy_src_t entropy_src_ = {.base_addr = dev().region()};
};

class InitTest : public DifEntropySrcTest {};

TEST_F(InitTest, BadArgs) {
  EXPECT_EQ(dif_entropy_src_init(dev().region(), nullptr), kDifBadArg);
}

TEST_F(InitTest, Init) {
  dif_entropy_src_t entropy;
  EXPECT_EQ(dif_entropy_src_init(dev().region(), &entropy), kDifOk);
}

class ConfigTest : public DifEntropySrcTest {
 protected:
  dif_entropy_src_config_t config_ = {
      .mode = kDifEntropySrcModeLfsr,
      .tests = {0},
      .reset_health_test_registers = false,
      .single_bit_mode = kDifEntropySrcSingleBitModeDisabled,
      .route_to_firmware = false,
      .fips_mode = false,
      .test_config = {0},
      .sample_rate = 64,
      .lfsr_seed = 4,
  };
};

TEST_F(ConfigTest, NullArgs) {
  EXPECT_EQ(dif_entropy_src_configure(nullptr, {}), kDifBadArg);
}

TEST_F(ConfigTest, LfsrSeedBadArg) {
  config_.lfsr_seed = 16;
  EXPECT_EQ(dif_entropy_src_configure(&entropy_src_, config_), kDifBadArg);
}

struct ConfigParams {
  dif_entropy_src_mode_t mode;
  dif_entropy_src_single_bit_mode_t single_bit_mode;
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
                     {ENTROPY_SRC_ENTROPY_CONTROL_ES_ROUTE_OFFSET,
                      (uint32_t)(test_param.route_to_firmware ? 0xa : 0x5)},
                     {ENTROPY_SRC_ENTROPY_CONTROL_ES_TYPE_OFFSET, 0x5},
                 });
  EXPECT_WRITE32(ENTROPY_SRC_FW_OV_CONTROL_REG_OFFSET, 0);

  // Current dif does not perform a read modified write
  // EXPECT_READ32(ENTROPY_SRC_CONF_REG_OFFSET, 0);

  uint32_t rng_bit_enable = test_param.expected_rng_bit_en ? 0xa : 0x5;
  // Current dif does not set these fields
  uint32_t lfsr_enable =
      test_param.expected_mode == kDifEntropySrcModeLfsr ? 0xa : 0x5;

  // uint32_t route_to_fw = test_param.route_to_firmware ? 0xa : 0x5;
  uint32_t enable =
      test_param.expected_mode != kDifEntropySrcModeDisabled ? 0xa : 0x5;
  uint32_t reset_ht = test_param.reset_health_test_registers ? 0xa : 0x5;
  EXPECT_WRITE32(
      ENTROPY_SRC_CONF_REG_OFFSET,
      {
          {ENTROPY_SRC_CONF_RNG_BIT_SEL_OFFSET, test_param.expected_rng_sel},
          {ENTROPY_SRC_CONF_RNG_BIT_ENABLE_OFFSET, rng_bit_enable},
          {ENTROPY_SRC_CONF_HEALTH_TEST_CLR_OFFSET, reset_ht},
          {ENTROPY_SRC_CONF_BOOT_BYPASS_DISABLE_OFFSET, 0x5},
          // Current dif doesn ot set these fields
          {ENTROPY_SRC_CONF_LFSR_ENABLE_OFFSET, lfsr_enable},
          //{ENTROPY_SRC_CONF_ENTROPY_DATA_REG_ENABLE_OFFSET, route_to_fw},
          {ENTROPY_SRC_CONF_ENABLE_OFFSET, enable},
      });

  EXPECT_EQ(dif_entropy_src_configure(&entropy_src_, config_), kDifOk);
}

INSTANTIATE_TEST_SUITE_P(
    ConfigTestAllParams, ConfigTestAllParams,
    testing::Values(
        // Test entropy mode.
        ConfigParams{kDifEntropySrcModeDisabled,
                     kDifEntropySrcSingleBitModeDisabled, false, false,
                     kDifEntropySrcModeDisabled, false, 0, 0},
        ConfigParams{kDifEntropySrcModePtrng,
                     kDifEntropySrcSingleBitModeDisabled, false, false, 1,
                     false, 0, 0},
        ConfigParams{kDifEntropySrcModeLfsr,
                     kDifEntropySrcSingleBitModeDisabled, false, false, 2,
                     false, 0, 4},
        // Test route_to_firmware
        ConfigParams{kDifEntropySrcModeLfsr,
                     kDifEntropySrcSingleBitModeDisabled, true, false, 2, false,
                     0, 4},
        // Test reset_health_test_registers
        ConfigParams{kDifEntropySrcModeLfsr,
                     kDifEntropySrcSingleBitModeDisabled, true, true, 2, false,
                     0, 4},
        // Test single_bit_mode
        ConfigParams{kDifEntropySrcModeLfsr, kDifEntropySrcSingleBitMode0, true,
                     true, 2, true, 0, 4},
        ConfigParams{kDifEntropySrcModeLfsr, kDifEntropySrcSingleBitMode1, true,
                     true, 2, true, 1, 4},
        ConfigParams{kDifEntropySrcModeLfsr, kDifEntropySrcSingleBitMode2, true,
                     true, 2, true, 2, 4},
        ConfigParams{kDifEntropySrcModeLfsr, kDifEntropySrcSingleBitMode3, true,
                     true, 2, true, 3, 4}));

class ReadTest : public DifEntropySrcTest {};

TEST_F(ReadTest, EntropyBadArg) {
  uint32_t word;
  EXPECT_EQ(dif_entropy_src_read(nullptr, &word), kDifBadArg);
}

TEST_F(ReadTest, WordBadArg) {
  EXPECT_EQ(dif_entropy_src_read(&entropy_src_, nullptr), kDifBadArg);
}

TEST_F(ReadTest, ReadDataUnAvailable) {
  EXPECT_READ32(ENTROPY_SRC_INTR_STATE_REG_OFFSET, 0);
  uint32_t got_word;
  EXPECT_EQ(dif_entropy_src_read(&entropy_src_, &got_word), kDifUnavailable);
}

TEST_F(ReadTest, ReadOk) {
  const uint32_t expected_word = 0x65585497;
  EXPECT_READ32(ENTROPY_SRC_INTR_STATE_REG_OFFSET,
                1 << ENTROPY_SRC_INTR_STATE_ES_ENTROPY_VALID_BIT);
  EXPECT_READ32(ENTROPY_SRC_ENTROPY_DATA_REG_OFFSET, expected_word);
  EXPECT_READ32(ENTROPY_SRC_INTR_STATE_REG_OFFSET,
                1 << ENTROPY_SRC_INTR_STATE_ES_ENTROPY_VALID_BIT);
  EXPECT_WRITE32(ENTROPY_SRC_INTR_STATE_REG_OFFSET,
                 {{ENTROPY_SRC_INTR_STATE_ES_ENTROPY_VALID_BIT, true}});

  uint32_t got_word;
  EXPECT_EQ(dif_entropy_src_read(&entropy_src_, &got_word), kDifOk);
  EXPECT_EQ(got_word, expected_word);
}

}  // namespace
}  // namespace dif_entropy_src_unittest
