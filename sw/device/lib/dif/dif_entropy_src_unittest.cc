// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_entropy_src.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/base/testing/mock_mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "entropy_src_regs.h"  // Generated

namespace dif_entropy_src_unittest {
namespace {

class DifEntropySrcTest : public testing::Test, public mock_mmio::MmioTest {
 protected:
  const dif_entropy_src_t entropy_src_ = {.base_addr = dev().region()};
};

class ConfigTest : public DifEntropySrcTest {
 protected:
  dif_entropy_src_config_t config_ = {
      .mode = kDifEntropySrcModePtrng,
      .tests = {0},
      .reset_health_test_registers = false,
      .single_bit_mode = kDifEntropySrcSingleBitModeDisabled,
      .route_to_firmware = false,
      .fips_mode = false,
      .test_config = {0},
      .fw_override =
          {
              .enable = false,
              .entropy_insert_enable = false,
              .buffer_threshold = kDifEntropyFifoIntDefaultThreshold,
          },
  };
};

TEST_F(ConfigTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_entropy_src_configure(nullptr, {}));
}

TEST_F(ConfigTest, InvalidFifoThreshold) {
  config_.fw_override.buffer_threshold = 65;
  EXPECT_DIF_BADARG(dif_entropy_src_configure(&entropy_src_, config_));
}

TEST_F(ConfigTest, InvalidFwOverrideSettings) {
  config_.fw_override.enable = false;
  config_.fw_override.entropy_insert_enable = true;
  EXPECT_DIF_BADARG(dif_entropy_src_configure(&entropy_src_, config_));
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

  EXPECT_WRITE32(ENTROPY_SRC_OBSERVE_FIFO_THRESH_REG_OFFSET,
                 config_.fw_override.buffer_threshold);
  EXPECT_WRITE32(
      ENTROPY_SRC_FW_OV_CONTROL_REG_OFFSET,
      {
          {ENTROPY_SRC_FW_OV_CONTROL_FW_OV_MODE_OFFSET,
           (uint32_t)(config_.fw_override.enable ? kMultiBitBool4True
                                                 : kMultiBitBool4False)},
          {ENTROPY_SRC_FW_OV_CONTROL_FW_OV_ENTROPY_INSERT_OFFSET,
           (uint32_t)(config_.fw_override.entropy_insert_enable
                          ? kMultiBitBool4True
                          : kMultiBitBool4False)},
      });

  EXPECT_WRITE32(
      ENTROPY_SRC_ENTROPY_CONTROL_REG_OFFSET,
      {
          {ENTROPY_SRC_ENTROPY_CONTROL_ES_ROUTE_OFFSET,
           (uint32_t)(test_param.route_to_firmware ? kMultiBitBool4True
                                                   : kMultiBitBool4False)},
          {ENTROPY_SRC_ENTROPY_CONTROL_ES_TYPE_OFFSET, kMultiBitBool4False},
      });

  // Current dif does not perform a read modified write
  // EXPECT_READ32(ENTROPY_SRC_CONF_REG_OFFSET, 0);

  uint32_t rng_bit_enable =
      test_param.expected_rng_bit_en ? kMultiBitBool4True : kMultiBitBool4False;
  uint32_t route_to_fw =
      test_param.route_to_firmware ? kMultiBitBool4True : kMultiBitBool4False;
  uint32_t enable = test_param.expected_mode != kDifEntropySrcModeDisabled
                        ? kMultiBitBool4True
                        : kMultiBitBool4False;
  EXPECT_WRITE32(
      ENTROPY_SRC_CONF_REG_OFFSET,
      {
          {ENTROPY_SRC_CONF_RNG_BIT_SEL_OFFSET, test_param.expected_rng_sel},
          {ENTROPY_SRC_CONF_RNG_BIT_ENABLE_OFFSET, rng_bit_enable},
          {ENTROPY_SRC_CONF_THRESHOLD_SCOPE_OFFSET, kMultiBitBool4False},
          {ENTROPY_SRC_CONF_ENTROPY_DATA_REG_ENABLE_OFFSET, route_to_fw},
          {ENTROPY_SRC_CONF_FIPS_ENABLE_OFFSET, enable},
      });

  EXPECT_WRITE32(ENTROPY_SRC_MODULE_ENABLE_REG_OFFSET,
                 {
                     {ENTROPY_SRC_MODULE_ENABLE_MODULE_ENABLE_OFFSET, enable},
                 });

  EXPECT_DIF_OK(dif_entropy_src_configure(&entropy_src_, config_));
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
        ConfigParams{kDifEntropySrcModePtrng,
                     kDifEntropySrcSingleBitModeDisabled, false, false, 2,
                     false, 0, 4},
        // Test route_to_firmware
        ConfigParams{kDifEntropySrcModePtrng,
                     kDifEntropySrcSingleBitModeDisabled, true, false, 2, false,
                     0, 4},
        // Test reset_health_test_registers
        ConfigParams{kDifEntropySrcModePtrng,
                     kDifEntropySrcSingleBitModeDisabled, true, true, 2, false,
                     0, 4},
        // Test single_bit_mode
        ConfigParams{kDifEntropySrcModePtrng, kDifEntropySrcSingleBitMode0,
                     true, true, 2, true, 0, 4},
        ConfigParams{kDifEntropySrcModePtrng, kDifEntropySrcSingleBitMode1,
                     true, true, 2, true, 1, 4},
        ConfigParams{kDifEntropySrcModePtrng, kDifEntropySrcSingleBitMode2,
                     true, true, 2, true, 2, 4},
        ConfigParams{kDifEntropySrcModePtrng, kDifEntropySrcSingleBitMode3,
                     true, true, 2, true, 3, 4}));

class ReadTest : public DifEntropySrcTest {};

TEST_F(ReadTest, EntropyBadArg) {
  uint32_t word;
  EXPECT_DIF_BADARG(dif_entropy_src_read(nullptr, &word));
}

TEST_F(ReadTest, WordBadArg) {
  EXPECT_DIF_BADARG(dif_entropy_src_read(&entropy_src_, nullptr));
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
  EXPECT_DIF_OK(dif_entropy_src_read(&entropy_src_, &got_word));
  EXPECT_EQ(got_word, expected_word);
}

}  // namespace
}  // namespace dif_entropy_src_unittest
