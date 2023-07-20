// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_entropy_src.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "entropy_src_regs.h"  // Generated

namespace dif_entropy_src_unittest {
namespace {

class EntropySrcTest : public testing::Test, public mock_mmio::MmioTest {
 protected:
  const dif_entropy_src_t entropy_src_ = {.base_addr = dev().region()};
};

class ConfigTest : public EntropySrcTest {
 protected:
  dif_entropy_src_config_t config_ = {
      .fips_enable = false,
      .route_to_firmware = false,
      .bypass_conditioner = false,
      .single_bit_mode = kDifEntropySrcSingleBitModeDisabled,
      .health_test_window_size = 1};
};

TEST_F(ConfigTest, NullHandle) {
  EXPECT_DIF_BADARG(
      dif_entropy_src_configure(nullptr, config_, kDifToggleEnabled));
}

TEST_F(ConfigTest, BadEnabled) {
  EXPECT_DIF_BADARG(dif_entropy_src_configure(&entropy_src_, config_,
                                              static_cast<dif_toggle_t>(2)));
}

TEST_F(ConfigTest, BadSingleBitMode) {
  config_.single_bit_mode = static_cast<dif_entropy_src_single_bit_mode_t>(5);
  EXPECT_DIF_BADARG(
      dif_entropy_src_configure(&entropy_src_, config_, kDifToggleEnabled));
}

TEST_F(ConfigTest, Locked) {
  EXPECT_READ32(ENTROPY_SRC_REGWEN_REG_OFFSET, 0);
  EXPECT_EQ(
      dif_entropy_src_configure(&entropy_src_, config_, kDifToggleEnabled),
      kDifLocked);
}

struct ConfigParams {
  bool fips_enable;
  bool route_to_firmware;
  bool bypass_conditioner;
  dif_entropy_src_single_bit_mode_t single_bit_mode;
  bool health_test_threshold_scope;
  uint16_t health_test_window_size;
  uint16_t alert_threshold;
  dif_toggle_t enabled;
};

class ConfigTestAllParams : public ConfigTest,
                            public testing::WithParamInterface<ConfigParams> {};

TEST_P(ConfigTestAllParams, ValidConfigurationMode) {
  const ConfigParams &test_param = GetParam();
  config_.fips_enable = test_param.fips_enable;
  config_.route_to_firmware = test_param.route_to_firmware;
  config_.bypass_conditioner = test_param.bypass_conditioner;
  config_.single_bit_mode = test_param.single_bit_mode;
  config_.health_test_threshold_scope = test_param.health_test_threshold_scope;
  config_.health_test_window_size = test_param.health_test_window_size;
  config_.alert_threshold = test_param.alert_threshold;

  EXPECT_READ32(ENTROPY_SRC_REGWEN_REG_OFFSET, 1);

  multi_bit_bool_t route_to_firmware_mubi =
      test_param.route_to_firmware ? kMultiBitBool4True : kMultiBitBool4False;
  multi_bit_bool_t bypass_conditioner_mubi =
      test_param.bypass_conditioner ? kMultiBitBool4True : kMultiBitBool4False;

  EXPECT_WRITE32(
      ENTROPY_SRC_ENTROPY_CONTROL_REG_OFFSET,
      {
          {ENTROPY_SRC_ENTROPY_CONTROL_ES_ROUTE_OFFSET, route_to_firmware_mubi},
          {ENTROPY_SRC_ENTROPY_CONTROL_ES_TYPE_OFFSET, bypass_conditioner_mubi},
      });

  multi_bit_bool_t fips_enable_mubi =
      test_param.fips_enable ? kMultiBitBool4True : kMultiBitBool4False;
  multi_bit_bool_t threshold_scope_mubi = test_param.health_test_threshold_scope
                                              ? kMultiBitBool4True
                                              : kMultiBitBool4False;
  multi_bit_bool_t rng_bit_enable_mubi =
      test_param.single_bit_mode == kDifEntropySrcSingleBitModeDisabled
          ? kMultiBitBool4False
          : kMultiBitBool4True;
  uint8_t rng_bit_sel =
      test_param.single_bit_mode == kDifEntropySrcSingleBitModeDisabled
          ? 0
          : test_param.single_bit_mode;

  EXPECT_WRITE32(
      ENTROPY_SRC_CONF_REG_OFFSET,
      {
          {ENTROPY_SRC_CONF_FIPS_ENABLE_OFFSET, fips_enable_mubi},
          {ENTROPY_SRC_CONF_ENTROPY_DATA_REG_ENABLE_OFFSET,
           route_to_firmware_mubi},
          {ENTROPY_SRC_CONF_THRESHOLD_SCOPE_OFFSET, threshold_scope_mubi},
          {ENTROPY_SRC_CONF_RNG_BIT_ENABLE_OFFSET, rng_bit_enable_mubi},
          {ENTROPY_SRC_CONF_RNG_BIT_SEL_OFFSET, rng_bit_sel},
      });

  EXPECT_WRITE32(ENTROPY_SRC_HEALTH_TEST_WINDOWS_REG_OFFSET,
                 {{ENTROPY_SRC_HEALTH_TEST_WINDOWS_BYPASS_WINDOW_OFFSET,
                   ENTROPY_SRC_HEALTH_TEST_WINDOWS_REG_RESVAL >>
                       ENTROPY_SRC_HEALTH_TEST_WINDOWS_BYPASS_WINDOW_OFFSET},
                  {ENTROPY_SRC_HEALTH_TEST_WINDOWS_FIPS_WINDOW_OFFSET,
                   test_param.health_test_window_size}});

  EXPECT_WRITE32(ENTROPY_SRC_ALERT_THRESHOLD_REG_OFFSET,
                 {{ENTROPY_SRC_ALERT_THRESHOLD_ALERT_THRESHOLD_INV_OFFSET,
                   static_cast<decltype(test_param.alert_threshold)>(
                       ~test_param.alert_threshold)},
                  {ENTROPY_SRC_ALERT_THRESHOLD_ALERT_THRESHOLD_OFFSET,
                   test_param.alert_threshold}});

  EXPECT_WRITE32(ENTROPY_SRC_MODULE_ENABLE_REG_OFFSET,
                 {
                     {ENTROPY_SRC_MODULE_ENABLE_MODULE_ENABLE_OFFSET,
                      dif_toggle_to_multi_bit_bool4(test_param.enabled)},
                 });

  EXPECT_DIF_OK(
      dif_entropy_src_configure(&entropy_src_, config_, test_param.enabled));
}

INSTANTIATE_TEST_SUITE_P(
    ConfigTestAllParams, ConfigTestAllParams,
    testing::Values(
        // Test FIPS enabled.
        ConfigParams{true, false, false, kDifEntropySrcSingleBitModeDisabled,
                     false, 0xFFFF, 2, kDifToggleEnabled},
        // Test route to firmware.
        ConfigParams{false, true, false, kDifEntropySrcSingleBitModeDisabled,
                     false, 2, kDifToggleEnabled},
        // Test bypass conditioner.
        ConfigParams{false, false, true, kDifEntropySrcSingleBitModeDisabled,
                     false, 2, kDifToggleEnabled},
        // Test single_bit_mode.
        ConfigParams{false, false, false, kDifEntropySrcSingleBitMode0, false,
                     512, 2, kDifToggleEnabled},
        ConfigParams{false, false, false, kDifEntropySrcSingleBitMode1, false,
                     256, 2, kDifToggleEnabled},
        ConfigParams{false, false, false, kDifEntropySrcSingleBitMode2, false,
                     128, 2, kDifToggleEnabled},
        ConfigParams{false, false, false, kDifEntropySrcSingleBitMode3, false,
                     64, 2, kDifToggleEnabled},
        // Test alerts disabled.
        ConfigParams{false, false, false, kDifEntropySrcSingleBitMode0, false,
                     1, 0, kDifToggleDisabled},
        // Test all disabled.
        ConfigParams{false, false, false, kDifEntropySrcSingleBitMode0, false,
                     1, 2, kDifToggleDisabled},
        // Test all enabled.
        ConfigParams{true, true, false, kDifEntropySrcSingleBitModeDisabled,
                     true, 32, 2, kDifToggleEnabled}));

class FwOverrideConfigTest : public EntropySrcTest {
 protected:
  dif_entropy_src_fw_override_config_t config_ = {
      .entropy_insert_enable = true,
      .buffer_threshold = ENTROPY_SRC_OBSERVE_FIFO_THRESH_REG_RESVAL,
  };
};

TEST_F(FwOverrideConfigTest, NullHandle) {
  EXPECT_DIF_BADARG(dif_entropy_src_fw_override_configure(nullptr, config_,
                                                          kDifToggleEnabled));
}

TEST_F(FwOverrideConfigTest, BadBufferThreshold) {
  config_.buffer_threshold =
      ENTROPY_SRC_OBSERVE_FIFO_THRESH_OBSERVE_FIFO_THRESH_MASK + 1;
  EXPECT_DIF_BADARG(dif_entropy_src_fw_override_configure(
      &entropy_src_, config_, kDifToggleEnabled));

  config_.buffer_threshold = 0;
  EXPECT_DIF_BADARG(dif_entropy_src_fw_override_configure(
      &entropy_src_, config_, kDifToggleEnabled));
}

TEST_F(FwOverrideConfigTest, BadEnabled) {
  EXPECT_DIF_BADARG(dif_entropy_src_fw_override_configure(
      &entropy_src_, config_, static_cast<dif_toggle_t>(2)));
}

TEST_F(FwOverrideConfigTest, Locked) {
  EXPECT_READ32(ENTROPY_SRC_REGWEN_REG_OFFSET, 0);
  EXPECT_EQ(dif_entropy_src_fw_override_configure(&entropy_src_, config_,
                                                  kDifToggleEnabled),
            kDifLocked);
}

TEST_F(FwOverrideConfigTest, Success) {
  EXPECT_READ32(ENTROPY_SRC_REGWEN_REG_OFFSET, 1);
  EXPECT_WRITE32(ENTROPY_SRC_OBSERVE_FIFO_THRESH_REG_OFFSET,
                 config_.buffer_threshold);
  EXPECT_WRITE32(ENTROPY_SRC_FW_OV_CONTROL_REG_OFFSET, 0x66);
  EXPECT_DIF_OK(dif_entropy_src_fw_override_configure(&entropy_src_, config_,
                                                      kDifToggleEnabled));

  EXPECT_READ32(ENTROPY_SRC_REGWEN_REG_OFFSET, 1);
  EXPECT_WRITE32(ENTROPY_SRC_OBSERVE_FIFO_THRESH_REG_OFFSET,
                 config_.buffer_threshold);
  EXPECT_WRITE32(ENTROPY_SRC_FW_OV_CONTROL_REG_OFFSET, 0x69);
  EXPECT_DIF_OK(dif_entropy_src_fw_override_configure(&entropy_src_, config_,
                                                      kDifToggleDisabled));
}

class HealthTestConfigTest : public EntropySrcTest {
 protected:
  dif_entropy_src_health_test_config_t config_ = {
      .test_type = kDifEntropySrcTestRepetitionCount,
      .high_threshold = 0xFFFF,
      .low_threshold = 0,
  };
};

TEST_F(HealthTestConfigTest, NullHandle) {
  EXPECT_DIF_BADARG(dif_entropy_src_health_test_configure(nullptr, config_));
}

TEST_F(HealthTestConfigTest, Locked) {
  EXPECT_READ32(ENTROPY_SRC_REGWEN_REG_OFFSET, 0);
  EXPECT_EQ(dif_entropy_src_health_test_configure(&entropy_src_, config_),
            kDifLocked);
}

TEST_F(HealthTestConfigTest, BadTestType) {
  config_.test_type = kDifEntropySrcTestNumVariants;
  EXPECT_READ32(ENTROPY_SRC_REGWEN_REG_OFFSET, 1);
  EXPECT_DIF_BADARG(
      dif_entropy_src_health_test_configure(&entropy_src_, config_));
}

TEST_F(HealthTestConfigTest, BadLowThreshold) {
  config_.low_threshold = 0x1;
  EXPECT_READ32(ENTROPY_SRC_REGWEN_REG_OFFSET, 1);
  EXPECT_DIF_BADARG(
      dif_entropy_src_health_test_configure(&entropy_src_, config_));
}

TEST_F(HealthTestConfigTest, SuccessOneThreshold) {
  EXPECT_READ32(ENTROPY_SRC_REGWEN_REG_OFFSET, 1);
  EXPECT_WRITE32(ENTROPY_SRC_REPCNT_THRESHOLDS_REG_OFFSET,
                 config_.high_threshold);
  EXPECT_DIF_OK(dif_entropy_src_health_test_configure(&entropy_src_, config_));
}

TEST_F(HealthTestConfigTest, SuccessTwoThresholds) {
  config_.test_type = kDifEntropySrcTestMarkov;
  config_.low_threshold = 0xABAB;
  EXPECT_READ32(ENTROPY_SRC_REGWEN_REG_OFFSET, 1);
  EXPECT_WRITE32(ENTROPY_SRC_MARKOV_HI_THRESHOLDS_REG_OFFSET,
                 config_.high_threshold);
  EXPECT_WRITE32(ENTROPY_SRC_MARKOV_LO_THRESHOLDS_REG_OFFSET,
                 config_.low_threshold);
  EXPECT_DIF_OK(dif_entropy_src_health_test_configure(&entropy_src_, config_));
}

class SetEnabledTest : public EntropySrcTest {};

TEST_F(SetEnabledTest, NullHandle) {
  EXPECT_DIF_BADARG(dif_entropy_src_set_enabled(nullptr, kDifToggleEnabled));
}

TEST_F(SetEnabledTest, BadToggle) {
  EXPECT_DIF_BADARG(
      dif_entropy_src_set_enabled(nullptr, static_cast<dif_toggle_t>(1)));
}

TEST_F(SetEnabledTest, Locked) {
  EXPECT_READ32(ENTROPY_SRC_ME_REGWEN_REG_OFFSET, 0);
  EXPECT_EQ(dif_entropy_src_set_enabled(&entropy_src_, kDifToggleEnabled),
            kDifLocked);
}

TEST_F(SetEnabledTest, Success) {
  // Enable.
  EXPECT_READ32(ENTROPY_SRC_ME_REGWEN_REG_OFFSET, 1);
  EXPECT_WRITE32(ENTROPY_SRC_MODULE_ENABLE_REG_OFFSET, kMultiBitBool4True);
  EXPECT_DIF_OK(dif_entropy_src_set_enabled(&entropy_src_, kDifToggleEnabled));

  // Disable.
  EXPECT_READ32(ENTROPY_SRC_ME_REGWEN_REG_OFFSET, 1);
  EXPECT_WRITE32(ENTROPY_SRC_MODULE_ENABLE_REG_OFFSET, kMultiBitBool4False);
  EXPECT_DIF_OK(dif_entropy_src_set_enabled(&entropy_src_, kDifToggleDisabled));
}

class LockTest : public EntropySrcTest {};

TEST_F(LockTest, NullHandle) {
  EXPECT_DIF_BADARG(dif_entropy_src_lock(nullptr));
}

TEST_F(LockTest, Success) {
  EXPECT_WRITE32(ENTROPY_SRC_ME_REGWEN_REG_OFFSET, 0);
  EXPECT_WRITE32(ENTROPY_SRC_SW_REGUPD_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_entropy_src_lock(&entropy_src_));
}

class IsLockedTest : public EntropySrcTest {};

TEST_F(IsLockedTest, NullArgs) {
  bool is_locked;
  EXPECT_DIF_BADARG(dif_entropy_src_is_locked(nullptr, &is_locked));
  EXPECT_DIF_BADARG(dif_entropy_src_is_locked(&entropy_src_, nullptr));
  EXPECT_DIF_BADARG(dif_entropy_src_is_locked(nullptr, nullptr));
}

TEST_F(IsLockedTest, BadState) {
  bool is_locked;
  EXPECT_READ32(ENTROPY_SRC_ME_REGWEN_REG_OFFSET, 1);
  EXPECT_READ32(ENTROPY_SRC_SW_REGUPD_REG_OFFSET, 0);
  EXPECT_EQ(dif_entropy_src_is_locked(&entropy_src_, &is_locked), kDifError);

  EXPECT_READ32(ENTROPY_SRC_ME_REGWEN_REG_OFFSET, 0);
  EXPECT_READ32(ENTROPY_SRC_SW_REGUPD_REG_OFFSET, 1);
  EXPECT_EQ(dif_entropy_src_is_locked(&entropy_src_, &is_locked), kDifError);
}

TEST_F(IsLockedTest, Success) {
  bool is_locked;
  EXPECT_READ32(ENTROPY_SRC_ME_REGWEN_REG_OFFSET, 0);
  EXPECT_READ32(ENTROPY_SRC_SW_REGUPD_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_entropy_src_is_locked(&entropy_src_, &is_locked));
  EXPECT_TRUE(is_locked);

  EXPECT_READ32(ENTROPY_SRC_ME_REGWEN_REG_OFFSET, 1);
  EXPECT_READ32(ENTROPY_SRC_SW_REGUPD_REG_OFFSET, 1);
  EXPECT_DIF_OK(dif_entropy_src_is_locked(&entropy_src_, &is_locked));
  EXPECT_FALSE(is_locked);
}

class HealthTestStatsGetTest : public EntropySrcTest {};

TEST_F(HealthTestStatsGetTest, NullArgs) {
  dif_entropy_src_health_test_stats_t stats;
  EXPECT_DIF_BADARG(dif_entropy_src_get_health_test_stats(nullptr, &stats));
  EXPECT_DIF_BADARG(
      dif_entropy_src_get_health_test_stats(&entropy_src_, nullptr));
  EXPECT_DIF_BADARG(dif_entropy_src_get_health_test_stats(nullptr, nullptr));
}

TEST_F(HealthTestStatsGetTest, Success) {
  dif_entropy_src_health_test_stats_t stats;

  EXPECT_READ32(ENTROPY_SRC_REPCNT_HI_WATERMARKS_REG_OFFSET, 10);
  EXPECT_READ32(ENTROPY_SRC_REPCNT_TOTAL_FAILS_REG_OFFSET, 10);

  EXPECT_READ32(ENTROPY_SRC_REPCNTS_HI_WATERMARKS_REG_OFFSET, 10);
  EXPECT_READ32(ENTROPY_SRC_REPCNTS_TOTAL_FAILS_REG_OFFSET, 10);

  EXPECT_READ32(ENTROPY_SRC_ADAPTP_HI_WATERMARKS_REG_OFFSET, 10);
  EXPECT_READ32(ENTROPY_SRC_ADAPTP_LO_WATERMARKS_REG_OFFSET, 10);
  EXPECT_READ32(ENTROPY_SRC_ADAPTP_HI_TOTAL_FAILS_REG_OFFSET, 10);
  EXPECT_READ32(ENTROPY_SRC_ADAPTP_LO_TOTAL_FAILS_REG_OFFSET, 10);

  EXPECT_READ32(ENTROPY_SRC_BUCKET_HI_WATERMARKS_REG_OFFSET, 10);
  EXPECT_READ32(ENTROPY_SRC_BUCKET_TOTAL_FAILS_REG_OFFSET, 10);

  EXPECT_READ32(ENTROPY_SRC_MARKOV_HI_WATERMARKS_REG_OFFSET, 10);
  EXPECT_READ32(ENTROPY_SRC_MARKOV_LO_WATERMARKS_REG_OFFSET, 10);
  EXPECT_READ32(ENTROPY_SRC_MARKOV_HI_TOTAL_FAILS_REG_OFFSET, 10);
  EXPECT_READ32(ENTROPY_SRC_MARKOV_LO_TOTAL_FAILS_REG_OFFSET, 10);

  EXPECT_READ32(ENTROPY_SRC_EXTHT_HI_WATERMARKS_REG_OFFSET, 10);
  EXPECT_READ32(ENTROPY_SRC_EXTHT_LO_WATERMARKS_REG_OFFSET, 10);
  EXPECT_READ32(ENTROPY_SRC_EXTHT_HI_TOTAL_FAILS_REG_OFFSET, 10);
  EXPECT_READ32(ENTROPY_SRC_EXTHT_LO_TOTAL_FAILS_REG_OFFSET, 10);

  EXPECT_DIF_OK(dif_entropy_src_get_health_test_stats(&entropy_src_, &stats));
  for (uint32_t i = 0; i < kDifEntropySrcTestNumVariants; ++i) {
    EXPECT_EQ(stats.high_watermark[i], 10);
    if (i == 2 || i == 4 || i == 5) {
      EXPECT_EQ(stats.low_watermark[i], 10);
    } else {
      EXPECT_EQ(stats.low_watermark[i], 0);
    }

    EXPECT_EQ(stats.high_fails[i], 10);
    if (i == 2 || i == 4 || i == 5) {
      EXPECT_EQ(stats.low_fails[i], 10);
    } else {
      EXPECT_EQ(stats.low_fails[i], 0);
    }
  }
}

class GetAlertFailCountsTest : public EntropySrcTest {};

TEST_F(GetAlertFailCountsTest, NullArgs) {
  dif_entropy_src_alert_fail_counts_t counts;
  EXPECT_DIF_BADARG(dif_entropy_src_get_alert_fail_counts(nullptr, &counts));
  EXPECT_DIF_BADARG(
      dif_entropy_src_get_alert_fail_counts(&entropy_src_, nullptr));
  EXPECT_DIF_BADARG(dif_entropy_src_get_alert_fail_counts(nullptr, nullptr));
}

TEST_F(GetAlertFailCountsTest, Success) {
  dif_entropy_src_alert_fail_counts_t counts;

  EXPECT_READ32(ENTROPY_SRC_ALERT_SUMMARY_FAIL_COUNTS_REG_OFFSET, 128);
  EXPECT_READ32(
      ENTROPY_SRC_ALERT_FAIL_COUNTS_REG_OFFSET,
      {{ENTROPY_SRC_ALERT_FAIL_COUNTS_REPCNT_FAIL_COUNT_OFFSET, 0xA},
       {ENTROPY_SRC_ALERT_FAIL_COUNTS_ADAPTP_HI_FAIL_COUNT_OFFSET, 0xC},
       {ENTROPY_SRC_ALERT_FAIL_COUNTS_ADAPTP_LO_FAIL_COUNT_OFFSET, 0xC},
       {ENTROPY_SRC_ALERT_FAIL_COUNTS_BUCKET_FAIL_COUNT_OFFSET, 0xD},
       {ENTROPY_SRC_ALERT_FAIL_COUNTS_MARKOV_HI_FAIL_COUNT_OFFSET, 0xE},
       {ENTROPY_SRC_ALERT_FAIL_COUNTS_MARKOV_LO_FAIL_COUNT_OFFSET, 0xE},
       {ENTROPY_SRC_ALERT_FAIL_COUNTS_REPCNTS_FAIL_COUNT_OFFSET, 0xB}});
  EXPECT_READ32(
      ENTROPY_SRC_EXTHT_FAIL_COUNTS_REG_OFFSET,
      {{ENTROPY_SRC_EXTHT_FAIL_COUNTS_EXTHT_HI_FAIL_COUNT_OFFSET, 0xF},
       {ENTROPY_SRC_EXTHT_FAIL_COUNTS_EXTHT_LO_FAIL_COUNT_OFFSET, 0xF}});
  EXPECT_DIF_OK(dif_entropy_src_get_alert_fail_counts(&entropy_src_, &counts));

  uint8_t num_fails = 0xA;
  for (uint32_t i = 0; i < kDifEntropySrcTestNumVariants; ++i) {
    EXPECT_EQ(counts.high_fails[i], num_fails);
    if (i == 2 || i == 4 || i == 5) {
      EXPECT_EQ(counts.low_fails[i], num_fails);
    } else {
      EXPECT_EQ(counts.low_fails[i], 0);
    }
    num_fails++;
  }
}

class IsEntropyAvailableTest : public EntropySrcTest {};

TEST_F(IsEntropyAvailableTest, NullHandle) {
  EXPECT_DIF_BADARG(dif_entropy_src_is_entropy_available(nullptr));
}

TEST_F(IsEntropyAvailableTest, Unavailable) {
  EXPECT_READ32(ENTROPY_SRC_INTR_STATE_REG_OFFSET,
                {{ENTROPY_SRC_INTR_STATE_ES_ENTROPY_VALID_BIT, false}});
  EXPECT_EQ(dif_entropy_src_is_entropy_available(&entropy_src_),
            kDifUnavailable);
}

TEST_F(IsEntropyAvailableTest, Available) {
  EXPECT_READ32(ENTROPY_SRC_INTR_STATE_REG_OFFSET,
                {{ENTROPY_SRC_INTR_STATE_ES_ENTROPY_VALID_BIT, true}});
  EXPECT_DIF_OK(dif_entropy_src_is_entropy_available(&entropy_src_));
}

class NonBlockingReadTest : public EntropySrcTest {};

TEST_F(NonBlockingReadTest, NullArgs) {
  uint32_t word;
  EXPECT_DIF_BADARG(dif_entropy_src_non_blocking_read(nullptr, &word));
  EXPECT_DIF_BADARG(dif_entropy_src_non_blocking_read(&entropy_src_, nullptr));
  EXPECT_DIF_BADARG(dif_entropy_src_non_blocking_read(nullptr, nullptr));
}

TEST_F(NonBlockingReadTest, DataUnavailable) {
  EXPECT_READ32(ENTROPY_SRC_INTR_STATE_REG_OFFSET, 0);
  uint32_t word;
  EXPECT_EQ(dif_entropy_src_non_blocking_read(&entropy_src_, &word),
            kDifUnavailable);
}

TEST_F(NonBlockingReadTest, Success) {
  const uint32_t expected_word = 0x65585497;
  EXPECT_READ32(ENTROPY_SRC_INTR_STATE_REG_OFFSET,
                1 << ENTROPY_SRC_INTR_STATE_ES_ENTROPY_VALID_BIT);
  EXPECT_READ32(ENTROPY_SRC_ENTROPY_DATA_REG_OFFSET, expected_word);
  EXPECT_READ32(ENTROPY_SRC_INTR_STATE_REG_OFFSET,
                1 << ENTROPY_SRC_INTR_STATE_ES_ENTROPY_VALID_BIT);
  EXPECT_WRITE32(ENTROPY_SRC_INTR_STATE_REG_OFFSET,
                 {{ENTROPY_SRC_INTR_STATE_ES_ENTROPY_VALID_BIT, true}});

  uint32_t word;
  EXPECT_DIF_OK(dif_entropy_src_non_blocking_read(&entropy_src_, &word));
  EXPECT_EQ(word, expected_word);
}

class ObserveFifoBlockingReadTest : public EntropySrcTest {};

TEST_F(ObserveFifoBlockingReadTest, NullHandle) {
  uint32_t buf[8];
  EXPECT_DIF_BADARG(
      dif_entropy_src_observe_fifo_blocking_read(nullptr, buf, 8));
}

TEST_F(ObserveFifoBlockingReadTest, BadLength) {
  uint32_t buf[8];
  EXPECT_READ32(ENTROPY_SRC_OBSERVE_FIFO_THRESH_REG_OFFSET, 7);
  EXPECT_DIF_BADARG(
      dif_entropy_src_observe_fifo_blocking_read(&entropy_src_, buf, 8));
}

TEST_F(ObserveFifoBlockingReadTest, BadConfig) {
  uint32_t buf[8];
  EXPECT_READ32(ENTROPY_SRC_OBSERVE_FIFO_THRESH_REG_OFFSET, 8);
  EXPECT_READ32(
      ENTROPY_SRC_FW_OV_CONTROL_REG_OFFSET,
      {{ENTROPY_SRC_FW_OV_CONTROL_FW_OV_ENTROPY_INSERT_OFFSET,
        kMultiBitBool4False},
       {ENTROPY_SRC_FW_OV_CONTROL_FW_OV_MODE_OFFSET, kMultiBitBool4False}});
  EXPECT_EQ(dif_entropy_src_observe_fifo_blocking_read(&entropy_src_, buf, 8),
            kDifError);
}

TEST_F(ObserveFifoBlockingReadTest, SuccessDataThroughAway) {
  uint32_t buf[4] = {0};
  EXPECT_READ32(ENTROPY_SRC_OBSERVE_FIFO_THRESH_REG_OFFSET, 4);
  EXPECT_READ32(
      ENTROPY_SRC_FW_OV_CONTROL_REG_OFFSET,
      {{ENTROPY_SRC_FW_OV_CONTROL_FW_OV_ENTROPY_INSERT_OFFSET,
        kMultiBitBool4False},
       {ENTROPY_SRC_FW_OV_CONTROL_FW_OV_MODE_OFFSET, kMultiBitBool4True}});
  EXPECT_READ32(ENTROPY_SRC_INTR_STATE_REG_OFFSET,
                {{ENTROPY_SRC_INTR_STATE_ES_OBSERVE_FIFO_READY_BIT, 1}});
  for (size_t i = 0; i < 4; ++i) {
    EXPECT_READ32(ENTROPY_SRC_FW_OV_RD_DATA_REG_OFFSET, i);
  }
  EXPECT_WRITE32(ENTROPY_SRC_INTR_STATE_REG_OFFSET,
                 {{ENTROPY_SRC_INTR_STATE_ES_OBSERVE_FIFO_READY_BIT, 1}});
  EXPECT_DIF_OK(
      dif_entropy_src_observe_fifo_blocking_read(&entropy_src_, nullptr, 4));
  for (size_t i = 0; i < 4; ++i) {
    EXPECT_EQ(buf[i], 0);
  }
}

TEST_F(ObserveFifoBlockingReadTest, SuccessDataSave) {
  uint32_t buf[4];
  EXPECT_READ32(ENTROPY_SRC_OBSERVE_FIFO_THRESH_REG_OFFSET, 4);
  EXPECT_READ32(
      ENTROPY_SRC_FW_OV_CONTROL_REG_OFFSET,
      {{ENTROPY_SRC_FW_OV_CONTROL_FW_OV_ENTROPY_INSERT_OFFSET,
        kMultiBitBool4False},
       {ENTROPY_SRC_FW_OV_CONTROL_FW_OV_MODE_OFFSET, kMultiBitBool4True}});
  EXPECT_READ32(ENTROPY_SRC_INTR_STATE_REG_OFFSET,
                {{ENTROPY_SRC_INTR_STATE_ES_OBSERVE_FIFO_READY_BIT, 1}});
  for (size_t i = 0; i < 4; ++i) {
    EXPECT_READ32(ENTROPY_SRC_FW_OV_RD_DATA_REG_OFFSET, i);
  }
  EXPECT_WRITE32(ENTROPY_SRC_INTR_STATE_REG_OFFSET,
                 {{ENTROPY_SRC_INTR_STATE_ES_OBSERVE_FIFO_READY_BIT, 1}});
  EXPECT_DIF_OK(
      dif_entropy_src_observe_fifo_blocking_read(&entropy_src_, buf, 4));
  for (size_t i = 0; i < 4; ++i) {
    EXPECT_EQ(buf[i], i);
  }
}

class ObserveFifoWriteTest : public EntropySrcTest {};

TEST_F(ObserveFifoWriteTest, NullArgs) {
  uint32_t buf[8] = {0};
  EXPECT_DIF_BADARG(
      dif_entropy_src_observe_fifo_write(nullptr, buf, 8, nullptr));
  EXPECT_DIF_BADARG(
      dif_entropy_src_observe_fifo_write(&entropy_src_, nullptr, 8, nullptr));
  EXPECT_DIF_BADARG(
      dif_entropy_src_observe_fifo_write(nullptr, nullptr, 8, nullptr));
}

TEST_F(ObserveFifoWriteTest, BadConfig) {
  uint32_t buf[8];

  // Firmware override mode not set.
  EXPECT_READ32(
      ENTROPY_SRC_FW_OV_CONTROL_REG_OFFSET,
      {{ENTROPY_SRC_FW_OV_CONTROL_FW_OV_ENTROPY_INSERT_OFFSET,
        kMultiBitBool4False},
       {ENTROPY_SRC_FW_OV_CONTROL_FW_OV_MODE_OFFSET, kMultiBitBool4False}});
  EXPECT_EQ(dif_entropy_src_observe_fifo_write(&entropy_src_, buf, 8, nullptr),
            kDifError);

  // Entropy insert mode not set.
  EXPECT_READ32(
      ENTROPY_SRC_FW_OV_CONTROL_REG_OFFSET,
      {{ENTROPY_SRC_FW_OV_CONTROL_FW_OV_ENTROPY_INSERT_OFFSET,
        kMultiBitBool4False},
       {ENTROPY_SRC_FW_OV_CONTROL_FW_OV_MODE_OFFSET, kMultiBitBool4True}});
  EXPECT_EQ(dif_entropy_src_observe_fifo_write(&entropy_src_, buf, 8, nullptr),
            kDifError);
}

TEST_F(ObserveFifoWriteTest, FifoFull) {
  uint32_t buf[4];
  size_t written = -1;
  EXPECT_READ32(
      ENTROPY_SRC_FW_OV_CONTROL_REG_OFFSET,
      {{ENTROPY_SRC_FW_OV_CONTROL_FW_OV_ENTROPY_INSERT_OFFSET,
        kMultiBitBool4True},
       {ENTROPY_SRC_FW_OV_CONTROL_FW_OV_MODE_OFFSET, kMultiBitBool4True}});
  EXPECT_READ32(ENTROPY_SRC_FW_OV_WR_FIFO_FULL_REG_OFFSET, 1);
  EXPECT_EQ(dif_entropy_src_observe_fifo_write(&entropy_src_, buf, 4, &written),
            kDifIpFifoFull);
  EXPECT_EQ(written, 0);
}

TEST_F(ObserveFifoWriteTest, Success) {
  uint32_t buf[4] = {1, 2, 3, 4};
  size_t written = -1;
  EXPECT_READ32(
      ENTROPY_SRC_FW_OV_CONTROL_REG_OFFSET,
      {{ENTROPY_SRC_FW_OV_CONTROL_FW_OV_ENTROPY_INSERT_OFFSET,
        kMultiBitBool4True},
       {ENTROPY_SRC_FW_OV_CONTROL_FW_OV_MODE_OFFSET, kMultiBitBool4True}});
  for (size_t i = 0; i < 4; ++i) {
    EXPECT_READ32(ENTROPY_SRC_FW_OV_WR_FIFO_FULL_REG_OFFSET, 0);
    EXPECT_WRITE32(ENTROPY_SRC_FW_OV_WR_DATA_REG_OFFSET, i + 1);
  }
  EXPECT_DIF_OK(
      dif_entropy_src_observe_fifo_write(&entropy_src_, buf, 4, &written));
  EXPECT_EQ(written, 4);
}

class ConditionerStartTest : public EntropySrcTest {};

TEST_F(ConditionerStartTest, NullHandle) {
  EXPECT_DIF_BADARG(dif_entropy_src_conditioner_start(nullptr));
}

TEST_F(ConditionerStartTest, ConditionerAlreadyStarted) {
  EXPECT_READ32(ENTROPY_SRC_FW_OV_SHA3_START_REG_OFFSET, kMultiBitBool4True);
  EXPECT_EQ(dif_entropy_src_conditioner_start(&entropy_src_), kDifUnavailable);
}

TEST_F(ConditionerStartTest, Success) {
  EXPECT_READ32(ENTROPY_SRC_FW_OV_SHA3_START_REG_OFFSET, kMultiBitBool4False);
  EXPECT_WRITE32(ENTROPY_SRC_FW_OV_SHA3_START_REG_OFFSET, kMultiBitBool4True);
  EXPECT_DIF_OK(dif_entropy_src_conditioner_start(&entropy_src_));
}

class ConditionerStopTest : public EntropySrcTest {};

TEST_F(ConditionerStopTest, NullHandle) {
  EXPECT_DIF_BADARG(dif_entropy_src_conditioner_stop(nullptr));
}

TEST_F(ConditionerStopTest, Success) {
  EXPECT_READ32(ENTROPY_SRC_FW_OV_WR_FIFO_FULL_REG_OFFSET, 0);
  EXPECT_WRITE32(ENTROPY_SRC_FW_OV_SHA3_START_REG_OFFSET, kMultiBitBool4False);
  EXPECT_DIF_OK(dif_entropy_src_conditioner_stop(&entropy_src_));
}

class IsFifoFullTest : public EntropySrcTest {};

TEST_F(IsFifoFullTest, NullArgs) {
  bool is_full;
  EXPECT_DIF_BADARG(dif_entropy_src_is_fifo_full(nullptr, &is_full));
  EXPECT_DIF_BADARG(dif_entropy_src_is_fifo_full(&entropy_src_, nullptr));
  EXPECT_DIF_BADARG(dif_entropy_src_is_fifo_full(nullptr, nullptr));
}

TEST_F(IsFifoFullTest, Success) {
  bool is_full;

  EXPECT_READ32(ENTROPY_SRC_FW_OV_WR_FIFO_FULL_REG_OFFSET, 1);
  EXPECT_DIF_OK(dif_entropy_src_is_fifo_full(&entropy_src_, &is_full));
  EXPECT_TRUE(is_full);

  EXPECT_READ32(ENTROPY_SRC_FW_OV_WR_FIFO_FULL_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_entropy_src_is_fifo_full(&entropy_src_, &is_full));
  EXPECT_FALSE(is_full);
}

class HasFifoOverflowedTest : public EntropySrcTest {};

TEST_F(HasFifoOverflowedTest, NullArgs) {
  bool has_overflowed;
  EXPECT_DIF_BADARG(
      dif_entropy_src_has_fifo_overflowed(nullptr, &has_overflowed));
  EXPECT_DIF_BADARG(
      dif_entropy_src_has_fifo_overflowed(&entropy_src_, nullptr));
  EXPECT_DIF_BADARG(dif_entropy_src_has_fifo_overflowed(nullptr, nullptr));
}

TEST_F(HasFifoOverflowedTest, Success) {
  bool has_overflowed;

  EXPECT_READ32(ENTROPY_SRC_FW_OV_RD_FIFO_OVERFLOW_REG_OFFSET, 1);
  EXPECT_DIF_OK(
      dif_entropy_src_has_fifo_overflowed(&entropy_src_, &has_overflowed));
  EXPECT_TRUE(has_overflowed);

  EXPECT_READ32(ENTROPY_SRC_FW_OV_RD_FIFO_OVERFLOW_REG_OFFSET, 0);
  EXPECT_DIF_OK(
      dif_entropy_src_has_fifo_overflowed(&entropy_src_, &has_overflowed));
  EXPECT_FALSE(has_overflowed);
}

class ClearFifoOverflowTest : public EntropySrcTest {};

TEST_F(ClearFifoOverflowTest, NullHandle) {
  EXPECT_DIF_BADARG(dif_entropy_src_clear_fifo_overflow(nullptr));
}

TEST_F(ClearFifoOverflowTest, Success) {
  EXPECT_WRITE32(ENTROPY_SRC_FW_OV_RD_FIFO_OVERFLOW_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_entropy_src_clear_fifo_overflow(&entropy_src_));
}

class ReadFifoDepthTest : public EntropySrcTest {};

TEST_F(ReadFifoDepthTest, EntropyBadArg) {
  uint32_t depth;
  EXPECT_DIF_BADARG(dif_entropy_src_get_fifo_depth(nullptr, &depth));
}

TEST_F(ReadFifoDepthTest, DepthBadArg) {
  EXPECT_DIF_BADARG(dif_entropy_src_get_fifo_depth(&entropy_src_, nullptr));
}

TEST_F(ReadFifoDepthTest, ReadSuccess) {
  EXPECT_READ32(ENTROPY_SRC_OBSERVE_FIFO_DEPTH_REG_OFFSET, 6);
  uint32_t depth;
  EXPECT_DIF_OK(dif_entropy_src_get_fifo_depth(&entropy_src_, &depth));
  EXPECT_EQ(depth, 6);
}

class GetDebugStateTest : public EntropySrcTest {};

TEST_F(GetDebugStateTest, NullArgs) {
  dif_entropy_src_debug_state_t debug_state;
  EXPECT_DIF_BADARG(dif_entropy_src_get_debug_state(nullptr, &debug_state));
  EXPECT_DIF_BADARG(dif_entropy_src_get_debug_state(&entropy_src_, nullptr));
  EXPECT_DIF_BADARG(dif_entropy_src_get_debug_state(nullptr, nullptr));
}

TEST_F(GetDebugStateTest, Success) {
  dif_entropy_src_debug_state_t debug_state;
  EXPECT_READ32(
      ENTROPY_SRC_DEBUG_STATUS_REG_OFFSET,
      {{ENTROPY_SRC_DEBUG_STATUS_MAIN_SM_BOOT_DONE_BIT, 1},
       {ENTROPY_SRC_DEBUG_STATUS_MAIN_SM_IDLE_BIT, 1},
       {ENTROPY_SRC_DEBUG_STATUS_SHA3_ERR_BIT, 1},
       {ENTROPY_SRC_DEBUG_STATUS_SHA3_ABSORBED_BIT, 1},
       {ENTROPY_SRC_DEBUG_STATUS_SHA3_SQUEEZING_BIT, 1},
       {ENTROPY_SRC_DEBUG_STATUS_SHA3_BLOCK_PR_BIT, 1},
       {ENTROPY_SRC_DEBUG_STATUS_SHA3_FSM_OFFSET, kDifEntropySrcSha3StateFlush},
       {ENTROPY_SRC_DEBUG_STATUS_ENTROPY_FIFO_DEPTH_OFFSET, 4}});
  EXPECT_DIF_OK(dif_entropy_src_get_debug_state(&entropy_src_, &debug_state));
  EXPECT_EQ(debug_state.entropy_fifo_depth, 4);
  EXPECT_EQ(debug_state.sha3_fsm_state, kDifEntropySrcSha3StateFlush);
  EXPECT_EQ(debug_state.sha3_block_processed, true);
  EXPECT_EQ(debug_state.sha3_squeezing, true);
  EXPECT_EQ(debug_state.sha3_absorbed, true);
  EXPECT_EQ(debug_state.sha3_error, true);
  EXPECT_EQ(debug_state.main_fsm_is_idle, true);
  EXPECT_EQ(debug_state.main_fsm_boot_done, true);
}

class GetRecoverableAlertsTest : public EntropySrcTest {};

TEST_F(GetRecoverableAlertsTest, NullArgs) {
  uint32_t alerts;
  EXPECT_DIF_BADARG(dif_entropy_src_get_recoverable_alerts(nullptr, &alerts));
  EXPECT_DIF_BADARG(
      dif_entropy_src_get_recoverable_alerts(&entropy_src_, nullptr));
  EXPECT_DIF_BADARG(dif_entropy_src_get_recoverable_alerts(nullptr, nullptr));
}

TEST_F(GetRecoverableAlertsTest, Success) {
  uint32_t alerts;
  EXPECT_READ32(ENTROPY_SRC_RECOV_ALERT_STS_REG_OFFSET,
                kDifEntropySrcAlertFwOvSha3StartField |
                    kDifEntropySrcAlertFwOvEntropyInsertField);
  EXPECT_DIF_OK(dif_entropy_src_get_recoverable_alerts(&entropy_src_, &alerts));
  EXPECT_EQ(alerts, kDifEntropySrcAlertFwOvSha3StartField |
                        kDifEntropySrcAlertFwOvEntropyInsertField);
}

class ClearRecoverableAlertsTest : public EntropySrcTest {};

TEST_F(ClearRecoverableAlertsTest, NullHandle) {
  uint32_t alerts = 0;
  EXPECT_DIF_BADARG(dif_entropy_src_clear_recoverable_alerts(nullptr, alerts));
}

TEST_F(ClearRecoverableAlertsTest, BadAlerts) {
  uint32_t alerts = 1U << 17;
  EXPECT_DIF_BADARG(
      dif_entropy_src_clear_recoverable_alerts(&entropy_src_, alerts));
}

TEST_F(ClearRecoverableAlertsTest, SuccessOneAlert) {
  uint32_t alerts = kDifEntropySrcAlertRngBitEnableField;
  EXPECT_READ32(ENTROPY_SRC_RECOV_ALERT_STS_REG_OFFSET, 0x2f);
  EXPECT_WRITE32(ENTROPY_SRC_RECOV_ALERT_STS_REG_OFFSET, 0xf);
  EXPECT_DIF_OK(
      dif_entropy_src_clear_recoverable_alerts(&entropy_src_, alerts));
}

TEST_F(ClearRecoverableAlertsTest, SuccessAllAlerts) {
  uint32_t alerts = kDifEntropySrcAlertAllAlerts;
  EXPECT_READ32(ENTROPY_SRC_RECOV_ALERT_STS_REG_OFFSET, 0x7faf);
  EXPECT_WRITE32(ENTROPY_SRC_RECOV_ALERT_STS_REG_OFFSET, 0);
  EXPECT_DIF_OK(
      dif_entropy_src_clear_recoverable_alerts(&entropy_src_, alerts));
}

class GetErrorsTest : public EntropySrcTest {};

TEST_F(GetErrorsTest, NullArgs) {
  uint32_t errors;
  EXPECT_DIF_BADARG(dif_entropy_src_get_errors(nullptr, &errors));
  EXPECT_DIF_BADARG(dif_entropy_src_get_errors(&entropy_src_, nullptr));
  EXPECT_DIF_BADARG(dif_entropy_src_get_errors(nullptr, nullptr));
}

TEST_F(GetErrorsTest, Success) {
  uint32_t errors;
  EXPECT_READ32(ENTROPY_SRC_ERR_CODE_REG_OFFSET, 0x30000003);
  EXPECT_DIF_OK(dif_entropy_src_get_errors(&entropy_src_, &errors));
  EXPECT_EQ(errors, kDifEntropySrcErrorRngFifoWrite |
                        kDifEntropySrcErrorRngFifoRead |
                        kDifEntropySrcErrorObserveFifoWrite |
                        kDifEntropySrcErrorObserveFifoRead);
}

class ForceErrorTest : public EntropySrcTest {};

TEST_F(ForceErrorTest, NullHandle) {
  EXPECT_DIF_BADARG(
      dif_entropy_src_error_force(nullptr, kDifEntropySrcErrorAckStateMachine));
}

TEST_F(ForceErrorTest, BadError) {
  EXPECT_DIF_BADARG(dif_entropy_src_error_force(
      &entropy_src_, static_cast<dif_entropy_src_error_t>(12)));
}

TEST_F(ForceErrorTest, Success) {
  EXPECT_WRITE32(ENTROPY_SRC_ERR_CODE_TEST_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_entropy_src_error_force(&entropy_src_,
                                            kDifEntropySrcErrorRngFifoWrite));

  EXPECT_WRITE32(ENTROPY_SRC_ERR_CODE_TEST_REG_OFFSET,
                 ENTROPY_SRC_ERR_CODE_ES_CNTR_ERR_BIT);
  EXPECT_DIF_OK(dif_entropy_src_error_force(
      &entropy_src_, kDifEntropySrcErrorHardenedCounter));
}

class GetMainFsmStateTest : public EntropySrcTest {};

TEST_F(GetMainFsmStateTest, NullArgs) {
  dif_entropy_src_main_fsm_t state;
  EXPECT_DIF_BADARG(dif_entropy_src_get_main_fsm_state(nullptr, &state));
  EXPECT_DIF_BADARG(dif_entropy_src_get_main_fsm_state(&entropy_src_, nullptr));
  EXPECT_DIF_BADARG(dif_entropy_src_get_main_fsm_state(nullptr, nullptr));
}

TEST_F(GetMainFsmStateTest, Success) {
  dif_entropy_src_main_fsm_t state;

  EXPECT_READ32(ENTROPY_SRC_MAIN_SM_STATE_REG_OFFSET,
                kDifEntropySrcMainFsmStateIdle);
  EXPECT_DIF_OK(dif_entropy_src_get_main_fsm_state(&entropy_src_, &state));
  EXPECT_EQ(state, kDifEntropySrcMainFsmStateIdle);

  EXPECT_READ32(ENTROPY_SRC_MAIN_SM_STATE_REG_OFFSET,
                kDifEntropySrcMainFsmStateError);
  EXPECT_DIF_OK(dif_entropy_src_get_main_fsm_state(&entropy_src_, &state));
  EXPECT_EQ(state, kDifEntropySrcMainFsmStateError);
}

}  // namespace
}  // namespace dif_entropy_src_unittest
