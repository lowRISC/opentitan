// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_pwrmgr.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/testing/mock_mmio.h"

#include "pwrmgr_regs.h"  // Generated

namespace dif_pwrmgr_unittest {
namespace {

/**
 * Returns a `uint32_t` with a single zero bit.
 */
uint32_t AllOnesExcept(uint32_t index) { return ~(1u << index); }

/**
 * Common constants used in tests.
 */
static constexpr std::array<dif_pwrmgr_toggle_t, 2> kAllToggles = {
    kDifPwrmgrToggleEnabled, kDifPwrmgrToggleDisabled};
static constexpr std::array<bool, 2> kAllBools = {true, false};
static constexpr dif_pwrmgr_toggle_t kBadToggle =
    static_cast<dif_pwrmgr_toggle_t>(kDifPwrmgrToggleDisabled + 1);
static constexpr dif_pwrmgr_irq_t kBadIrq =
    static_cast<dif_pwrmgr_irq_t>(kDifPwrmgrIrqLast + 1);
static constexpr dif_pwrmgr_req_type_t kBadReqType =
    static_cast<dif_pwrmgr_req_type_t>(kDifPwrmgrReqTypeReset + 1);
static constexpr dif_pwrmgr_domain_config_t kBadConfig =
    std::numeric_limits<uint8_t>::max();
static constexpr dif_pwrmgr_request_sources_t kBadSources =
    std::numeric_limits<uint32_t>::max();

class DifPwrmgrTest : public testing::Test, public mock_mmio::MmioTest {
 protected:
  /**
   * Parameters for initializing a `dif_pwrmgr_t`.
   */
  const dif_pwrmgr_params_t params_ = {.base_addr = dev().region()};
};

class InitTest : public DifPwrmgrTest {};

TEST_F(InitTest, BadArgs) {
  EXPECT_EQ(dif_pwrmgr_init(params_, nullptr), kDifPwrmgrBadArg);
}

TEST_F(InitTest, Init) {
  dif_pwrmgr_t pwrmgr;
  EXPECT_EQ(dif_pwrmgr_init(params_, &pwrmgr), kDifPwrmgrOk);
}

// Base class for the rest of the tests in this file, provides a
// `dif_gpio_t` instance.
class DifPwrmgrInitialized : public DifPwrmgrTest {
 protected:
  /**
   * Expectations for functions that need to sync data to slow clock domain.
   *
   * Sync is triggered by writing a 1 to the CFG_CDC_SYNC register, which is
   * reset back to 0 by the hardware when the operation is complete.
   */
  void ExpectSync() {
    EXPECT_WRITE32(PWRMGR_CFG_CDC_SYNC_REG_OFFSET, 1);
    // Insert a small random delay.
    uint8_t rand_delay = dev().GarbageMemory<uint32_t>() & 0x7F;
    for (uint8_t i = 0; i < rand_delay; ++i) {
      EXPECT_READ32(PWRMGR_CFG_CDC_SYNC_REG_OFFSET, 1);
    }
    EXPECT_READ32(PWRMGR_CFG_CDC_SYNC_REG_OFFSET, 0);
  }

  /**
   * Initialized `dif_pwrmgr_t` used in tests.
   */
  const dif_pwrmgr_t pwrmgr_ = {.params = params_};
};

class LowPowerTest : public DifPwrmgrInitialized {};

TEST_F(LowPowerTest, SetBadArgs) {
  EXPECT_EQ(dif_pwrmgr_low_power_set_enabled(nullptr, kDifPwrmgrToggleEnabled),
            kDifPwrmgrConfigBadArg);
  EXPECT_EQ(dif_pwrmgr_low_power_set_enabled(&pwrmgr_, kBadToggle),
            kDifPwrmgrConfigBadArg);
  EXPECT_EQ(dif_pwrmgr_low_power_set_enabled(nullptr, kBadToggle),
            kDifPwrmgrConfigBadArg);
}

TEST_F(LowPowerTest, SetLocked) {
  for (auto toggle : kAllToggles) {
    EXPECT_READ32(PWRMGR_CTRL_CFG_REGWEN_REG_OFFSET,
                  AllOnesExcept(PWRMGR_CTRL_CFG_REGWEN_EN_BIT));

    EXPECT_EQ(dif_pwrmgr_low_power_set_enabled(&pwrmgr_, toggle),
              kDifPwrMgrConfigLocked);
  }
}

TEST_F(LowPowerTest, Set) {
  for (auto toggle : kAllToggles) {
    EXPECT_READ32(PWRMGR_CTRL_CFG_REGWEN_REG_OFFSET,
                  {{
                      .offset = PWRMGR_CTRL_CFG_REGWEN_EN_BIT,
                      .value = 1,
                  }});
    EXPECT_MASK32(PWRMGR_CONTROL_REG_OFFSET,
                  {{
                      .offset = PWRMGR_CONTROL_LOW_POWER_HINT_BIT,
                      .mask = 1,
                      .value = (toggle == kDifPwrmgrToggleEnabled),
                  }});
    ExpectSync();

    EXPECT_EQ(dif_pwrmgr_low_power_set_enabled(&pwrmgr_, toggle),
              kDifPwrmgrConfigOk);
  }
}

TEST_F(LowPowerTest, GetBadArgs) {
  dif_pwrmgr_toggle_t state;

  EXPECT_EQ(dif_pwrmgr_low_power_get_enabled(nullptr, &state),
            kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_low_power_get_enabled(&pwrmgr_, nullptr),
            kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_low_power_get_enabled(nullptr, nullptr),
            kDifPwrmgrBadArg);
}

TEST_F(LowPowerTest, Get) {
  for (auto toggle : kAllToggles) {
    dif_pwrmgr_toggle_t state;

    EXPECT_READ32(PWRMGR_CONTROL_REG_OFFSET,
                  {{
                      .offset = PWRMGR_CONTROL_LOW_POWER_HINT_BIT,
                      .value = (toggle == kDifPwrmgrToggleEnabled),
                  }});

    EXPECT_EQ(dif_pwrmgr_low_power_get_enabled(&pwrmgr_, &state), kDifPwrmgrOk);
    EXPECT_EQ(state, toggle);
  }
}

class DomainConfig : public DifPwrmgrInitialized {
 protected:
  /**
   * Constants used in set and get tests.
   */
  static constexpr bitfield_field32_t kConfigBitfield{
      .mask = kDifPwrmgrDomainOptionCoreClockInLowPower |
              kDifPwrmgrDomainOptionIoClockInLowPower |
              kDifPwrmgrDomainOptionUsbClockInLowPower |
              kDifPwrmgrDomainOptionUsbClockInActivePower |
              kDifPwrmgrDomainOptionMainPowerInLowPower,
      .index = PWRMGR_CONTROL_CORE_CLK_EN_BIT,
  };
  static constexpr std::array<dif_pwrmgr_domain_config_t, 4> kConfigs = {
      // All disabled.
      0,
      // All enabled.
      kDifPwrmgrDomainOptionCoreClockInLowPower |
          kDifPwrmgrDomainOptionIoClockInLowPower |
          kDifPwrmgrDomainOptionUsbClockInLowPower |
          kDifPwrmgrDomainOptionUsbClockInActivePower |
          kDifPwrmgrDomainOptionMainPowerInLowPower,
      // Some enabled.
      kDifPwrmgrDomainOptionCoreClockInLowPower |
          kDifPwrmgrDomainOptionUsbClockInLowPower |
          kDifPwrmgrDomainOptionMainPowerInLowPower,
      // Some enabled.
      kDifPwrmgrDomainOptionIoClockInLowPower |
          kDifPwrmgrDomainOptionUsbClockInActivePower,
  };
};
// We need this definition for the `for` loops.
constexpr std::array<dif_pwrmgr_domain_config_t, 4> DomainConfig::kConfigs;

TEST_F(DomainConfig, SetBadArgs) {
  EXPECT_EQ(dif_pwrmgr_set_domain_config(nullptr, 0), kDifPwrmgrConfigBadArg);
  EXPECT_EQ(dif_pwrmgr_set_domain_config(&pwrmgr_, kBadConfig),
            kDifPwrmgrConfigBadArg);
  EXPECT_EQ(dif_pwrmgr_set_domain_config(nullptr, kBadConfig),
            kDifPwrmgrConfigBadArg);
}

TEST_F(DomainConfig, SetLocked) {
  EXPECT_READ32(PWRMGR_CTRL_CFG_REGWEN_REG_OFFSET,
                AllOnesExcept(PWRMGR_WAKEUP_EN_REGWEN_EN_BIT));

  EXPECT_EQ(dif_pwrmgr_set_domain_config(&pwrmgr_, 0), kDifPwrMgrConfigLocked);
}

TEST_F(DomainConfig, Set) {
  for (auto config : kConfigs) {
    EXPECT_READ32(PWRMGR_CTRL_CFG_REGWEN_REG_OFFSET,
                  {{
                      .offset = PWRMGR_CTRL_CFG_REGWEN_EN_BIT,
                      .value = 1,
                  }});
    EXPECT_MASK32(PWRMGR_CONTROL_REG_OFFSET,
                  {{
                      .offset = kConfigBitfield.index,
                      .mask = kConfigBitfield.mask,
                      .value = config,
                  }});
    ExpectSync();

    EXPECT_EQ(dif_pwrmgr_set_domain_config(&pwrmgr_, config), kDifPwrmgrOk);
  }
}

TEST_F(DomainConfig, GetBadArgs) {
  dif_pwrmgr_domain_config_t config;
  EXPECT_EQ(dif_pwrmgr_get_domain_config(nullptr, &config),
            kDifPwrmgrConfigBadArg);
  EXPECT_EQ(dif_pwrmgr_get_domain_config(&pwrmgr_, nullptr),
            kDifPwrmgrConfigBadArg);
  EXPECT_EQ(dif_pwrmgr_get_domain_config(nullptr, nullptr),
            kDifPwrmgrConfigBadArg);
}

TEST_F(DomainConfig, Get) {
  for (auto exp_config : kConfigs) {
    EXPECT_READ32(PWRMGR_CONTROL_REG_OFFSET,
                  {{
                      .offset = kConfigBitfield.index,
                      .value = exp_config,
                  }});

    dif_pwrmgr_domain_config_t act_config;
    EXPECT_EQ(dif_pwrmgr_get_domain_config(&pwrmgr_, &act_config),
              kDifPwrmgrOk);
    EXPECT_EQ(act_config, exp_config);
  }
}

class RequestSources : public DifPwrmgrInitialized {
 protected:
  /**
   * Constants used in set and get tests.
   */
  static constexpr std::array<dif_pwrmgr_request_sources_t, 2> kWakeupSources =
      {
          // No sources.
          0,
          // All sources.
          kDifPwrmgrWakeupRequestSourceOne,
      };
  static constexpr std::array<dif_pwrmgr_request_sources_t, 2> kResetSources = {
      // No sources.
      0,
      // All sources.
      kDifPwrmgrResetRequestSourceOne,
  };
};
// We need these definitions for the `for` loops.
constexpr std::array<dif_pwrmgr_request_sources_t, 2>
    RequestSources::kWakeupSources;
constexpr std::array<dif_pwrmgr_request_sources_t, 2>
    RequestSources::kResetSources;

TEST_F(RequestSources, SetBadArgs) {
  EXPECT_EQ(dif_pwrmgr_set_request_sources(nullptr, kDifPwrmgrReqTypeWakeup,
                                           kDifPwrmgrWakeupRequestSourceOne),
            kDifPwrmgrConfigBadArg);
  EXPECT_EQ(dif_pwrmgr_set_request_sources(&pwrmgr_, kBadReqType,
                                           kDifPwrmgrWakeupRequestSourceOne),
            kDifPwrmgrConfigBadArg);
  EXPECT_EQ(dif_pwrmgr_set_request_sources(&pwrmgr_, kDifPwrmgrReqTypeWakeup,
                                           kBadSources),
            kDifPwrmgrConfigBadArg);
  EXPECT_EQ(dif_pwrmgr_set_request_sources(nullptr, kBadReqType,
                                           kDifPwrmgrWakeupRequestSourceOne),
            kDifPwrmgrConfigBadArg);
  EXPECT_EQ(dif_pwrmgr_set_request_sources(nullptr, kDifPwrmgrReqTypeWakeup,
                                           kBadSources),
            kDifPwrmgrConfigBadArg);
  EXPECT_EQ(dif_pwrmgr_set_request_sources(&pwrmgr_, kBadReqType, kBadSources),
            kDifPwrmgrConfigBadArg);
  EXPECT_EQ(dif_pwrmgr_set_request_sources(nullptr, kBadReqType, kBadSources),
            kDifPwrmgrConfigBadArg);
}

TEST_F(RequestSources, SetWakeupLocked) {
  EXPECT_READ32(PWRMGR_WAKEUP_EN_REGWEN_REG_OFFSET,
                AllOnesExcept(PWRMGR_WAKEUP_EN_REGWEN_EN_BIT));

  EXPECT_EQ(dif_pwrmgr_set_request_sources(&pwrmgr_, kDifPwrmgrReqTypeWakeup,
                                           kDifPwrmgrWakeupRequestSourceOne),
            kDifPwrMgrConfigLocked);
}

TEST_F(RequestSources, SetResetLocked) {
  EXPECT_READ32(PWRMGR_RESET_EN_REGWEN_REG_OFFSET,
                AllOnesExcept(PWRMGR_RESET_EN_REGWEN_EN_BIT));

  EXPECT_EQ(dif_pwrmgr_set_request_sources(&pwrmgr_, kDifPwrmgrReqTypeReset,
                                           kDifPwrmgrResetRequestSourceOne),
            kDifPwrMgrConfigLocked);
}

TEST_F(RequestSources, SetWakeup) {
  EXPECT_READ32(PWRMGR_WAKEUP_EN_REGWEN_REG_OFFSET,
                {{
                    .offset = PWRMGR_WAKEUP_EN_REGWEN_EN_BIT,
                    .value = 1,
                }});
  EXPECT_WRITE32(PWRMGR_WAKEUP_EN_REG_OFFSET, kDifPwrmgrWakeupRequestSourceOne);
  ExpectSync();

  EXPECT_EQ(dif_pwrmgr_set_request_sources(&pwrmgr_, kDifPwrmgrReqTypeWakeup,
                                           kDifPwrmgrWakeupRequestSourceOne),
            kDifPwrmgrConfigOk);
}

TEST_F(RequestSources, SetReset) {
  EXPECT_READ32(PWRMGR_RESET_EN_REGWEN_REG_OFFSET,
                {{
                    .offset = PWRMGR_RESET_EN_REGWEN_EN_BIT,
                    .value = 1,
                }});
  EXPECT_WRITE32(PWRMGR_RESET_EN_REG_OFFSET, kDifPwrmgrResetRequestSourceOne);
  ExpectSync();

  EXPECT_EQ(dif_pwrmgr_set_request_sources(&pwrmgr_, kDifPwrmgrReqTypeReset,
                                           kDifPwrmgrResetRequestSourceOne),
            kDifPwrmgrConfigOk);
}

TEST_F(RequestSources, GetBadArgs) {
  dif_pwrmgr_request_sources_t sources;

  EXPECT_EQ(dif_pwrmgr_get_request_sources(nullptr, kDifPwrmgrReqTypeWakeup,
                                           &sources),
            kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_get_request_sources(&pwrmgr_, kBadReqType, &sources),
            kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_get_request_sources(&pwrmgr_, kDifPwrmgrReqTypeWakeup,
                                           nullptr),
            kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_get_request_sources(nullptr, kBadReqType, &sources),
            kDifPwrmgrBadArg);
  EXPECT_EQ(
      dif_pwrmgr_get_request_sources(nullptr, kDifPwrmgrReqTypeWakeup, nullptr),
      kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_get_request_sources(&pwrmgr_, kBadReqType, nullptr),
            kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_get_request_sources(nullptr, kBadReqType, nullptr),
            kDifPwrmgrBadArg);
}

TEST_F(RequestSources, GetWakeup) {
  for (auto exp_sources : kWakeupSources) {
    EXPECT_READ32(PWRMGR_WAKEUP_EN_REG_OFFSET, exp_sources);

    dif_pwrmgr_request_sources_t act_sources = 0;
    EXPECT_EQ(dif_pwrmgr_get_request_sources(&pwrmgr_, kDifPwrmgrReqTypeWakeup,
                                             &act_sources),
              kDifPwrmgrOk);
    EXPECT_EQ(act_sources, exp_sources);
  }
}

TEST_F(RequestSources, GetReset) {
  for (auto exp_sources : kResetSources) {
    EXPECT_READ32(PWRMGR_RESET_EN_REG_OFFSET, exp_sources);

    dif_pwrmgr_request_sources_t act_sources = 0;
    EXPECT_EQ(dif_pwrmgr_get_request_sources(&pwrmgr_, kDifPwrmgrReqTypeReset,
                                             &act_sources),
              kDifPwrmgrOk);
    EXPECT_EQ(act_sources, exp_sources);
  }
}

TEST_F(RequestSources, GetCurrentBadArgs) {
  dif_pwrmgr_request_sources_t sources;

  EXPECT_EQ(dif_pwrmgr_get_current_request_sources(
                nullptr, kDifPwrmgrReqTypeWakeup, &sources),
            kDifPwrmgrBadArg);
  EXPECT_EQ(
      dif_pwrmgr_get_current_request_sources(&pwrmgr_, kBadReqType, &sources),
      kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_get_current_request_sources(
                &pwrmgr_, kDifPwrmgrReqTypeWakeup, nullptr),
            kDifPwrmgrBadArg);
  EXPECT_EQ(
      dif_pwrmgr_get_current_request_sources(nullptr, kBadReqType, &sources),
      kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_get_current_request_sources(
                nullptr, kDifPwrmgrReqTypeWakeup, nullptr),
            kDifPwrmgrBadArg);
  EXPECT_EQ(
      dif_pwrmgr_get_current_request_sources(&pwrmgr_, kBadReqType, nullptr),
      kDifPwrmgrBadArg);
  EXPECT_EQ(
      dif_pwrmgr_get_current_request_sources(nullptr, kBadReqType, nullptr),
      kDifPwrmgrBadArg);
}

TEST_F(RequestSources, GetCurrentWakeup) {
  for (auto exp_sources : kWakeupSources) {
    EXPECT_READ32(PWRMGR_WAKE_STATUS_REG_OFFSET, exp_sources);

    dif_pwrmgr_request_sources_t act_sources = 0;
    EXPECT_EQ(dif_pwrmgr_get_current_request_sources(
                  &pwrmgr_, kDifPwrmgrReqTypeWakeup, &act_sources),
              kDifPwrmgrOk);
    EXPECT_EQ(act_sources, exp_sources);
  }
}

TEST_F(RequestSources, GetCurrentReset) {
  for (auto exp_sources : kResetSources) {
    EXPECT_READ32(PWRMGR_RESET_STATUS_REG_OFFSET, exp_sources);

    dif_pwrmgr_request_sources_t act_sources = 0;
    EXPECT_EQ(dif_pwrmgr_get_current_request_sources(
                  &pwrmgr_, kDifPwrmgrReqTypeReset, &act_sources),
              kDifPwrmgrOk);
    EXPECT_EQ(act_sources, exp_sources);
  }
}

TEST_F(RequestSources, LockBadArgs) {
  EXPECT_EQ(dif_pwrmgr_request_sources_lock(nullptr, kDifPwrmgrReqTypeWakeup),
            kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_request_sources_lock(&pwrmgr_, kBadReqType),
            kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_request_sources_lock(nullptr, kBadReqType),
            kDifPwrmgrBadArg);
}

TEST_F(RequestSources, LockWakeup) {
  EXPECT_WRITE32(PWRMGR_WAKEUP_EN_REGWEN_REG_OFFSET, 0);

  EXPECT_EQ(dif_pwrmgr_request_sources_lock(&pwrmgr_, kDifPwrmgrReqTypeWakeup),
            kDifPwrmgrOk);
}

TEST_F(RequestSources, LockReset) {
  EXPECT_WRITE32(PWRMGR_RESET_EN_REGWEN_REG_OFFSET, 0);

  EXPECT_EQ(dif_pwrmgr_request_sources_lock(&pwrmgr_, kDifPwrmgrReqTypeReset),
            kDifPwrmgrOk);
}

TEST_F(RequestSources, IsLockedBadArgs) {
  bool is_locked;

  EXPECT_EQ(dif_pwrmgr_request_sources_is_locked(
                nullptr, kDifPwrmgrReqTypeWakeup, &is_locked),
            kDifPwrmgrBadArg);
  EXPECT_EQ(
      dif_pwrmgr_request_sources_is_locked(&pwrmgr_, kBadReqType, &is_locked),
      kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_request_sources_is_locked(
                &pwrmgr_, kDifPwrmgrReqTypeWakeup, nullptr),
            kDifPwrmgrBadArg);
  EXPECT_EQ(
      dif_pwrmgr_request_sources_is_locked(nullptr, kBadReqType, &is_locked),
      kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_request_sources_is_locked(
                nullptr, kDifPwrmgrReqTypeWakeup, nullptr),
            kDifPwrmgrBadArg);
  EXPECT_EQ(
      dif_pwrmgr_request_sources_is_locked(&pwrmgr_, kBadReqType, nullptr),
      kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_request_sources_is_locked(nullptr, kBadReqType, nullptr),
            kDifPwrmgrBadArg);
}

TEST_F(RequestSources, IsLockedWakeup) {
  for (auto exp_val : kAllBools) {
    EXPECT_READ32(PWRMGR_WAKEUP_EN_REGWEN_REG_OFFSET,
                  {{
                      .offset = PWRMGR_WAKEUP_EN_REGWEN_EN_BIT,
                      .value = !exp_val,
                  }});

    bool is_locked = !exp_val;
    EXPECT_EQ(dif_pwrmgr_request_sources_is_locked(
                  &pwrmgr_, kDifPwrmgrReqTypeWakeup, &is_locked),
              kDifPwrmgrOk);
    EXPECT_EQ(is_locked, exp_val);
  }
}

TEST_F(RequestSources, IsLockedReset) {
  for (auto exp_val : kAllBools) {
    EXPECT_READ32(PWRMGR_RESET_EN_REGWEN_REG_OFFSET,
                  {{
                      .offset = PWRMGR_RESET_EN_REGWEN_EN_BIT,
                      .value = !exp_val,
                  }});

    bool is_locked = !exp_val;
    EXPECT_EQ(dif_pwrmgr_request_sources_is_locked(
                  &pwrmgr_, kDifPwrmgrReqTypeReset, &is_locked),
              kDifPwrmgrOk);
    EXPECT_EQ(is_locked, exp_val);
  }
}

class WakeupRecording : public DifPwrmgrInitialized {};

TEST_F(WakeupRecording, SetEnabledBadArgs) {
  EXPECT_EQ(dif_pwrmgr_wakeup_request_recording_set_enabled(
                nullptr, kDifPwrmgrToggleEnabled),
            kDifPwrmgrBadArg);
  EXPECT_EQ(
      dif_pwrmgr_wakeup_request_recording_set_enabled(&pwrmgr_, kBadToggle),
      kDifPwrmgrBadArg);
  EXPECT_EQ(
      dif_pwrmgr_wakeup_request_recording_set_enabled(nullptr, kBadToggle),
      kDifPwrmgrBadArg);
}

TEST_F(WakeupRecording, SetEnabled) {
  for (auto new_state : kAllToggles) {
    EXPECT_WRITE32(PWRMGR_WAKE_INFO_CAPTURE_DIS_REG_OFFSET,
                   {{
                       .offset = PWRMGR_WAKE_INFO_CAPTURE_DIS_VAL_BIT,
                       .value = (new_state == kDifPwrmgrToggleDisabled),
                   }});

    EXPECT_EQ(
        dif_pwrmgr_wakeup_request_recording_set_enabled(&pwrmgr_, new_state),
        kDifPwrmgrOk);
  }
}

TEST_F(WakeupRecording, GetEnabledBadArgs) {
  dif_pwrmgr_toggle_t is_enabled;

  EXPECT_EQ(
      dif_pwrmgr_wakeup_request_recording_get_enabled(nullptr, &is_enabled),
      kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_wakeup_request_recording_get_enabled(&pwrmgr_, nullptr),
            kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_wakeup_request_recording_get_enabled(nullptr, nullptr),
            kDifPwrmgrBadArg);
}

TEST_F(WakeupRecording, GetEnabled) {
  for (auto exp_val : kAllToggles) {
    EXPECT_READ32(PWRMGR_WAKE_INFO_CAPTURE_DIS_REG_OFFSET,
                  {{
                      .offset = PWRMGR_WAKE_INFO_CAPTURE_DIS_VAL_BIT,
                      .value = (exp_val == kDifPwrmgrToggleDisabled),
                  }});

    dif_pwrmgr_toggle_t is_enabled = (exp_val == kDifPwrmgrToggleEnabled)
                                         ? kDifPwrmgrToggleDisabled
                                         : kDifPwrmgrToggleEnabled;
    EXPECT_EQ(
        dif_pwrmgr_wakeup_request_recording_get_enabled(&pwrmgr_, &is_enabled),
        kDifPwrmgrOk);
    EXPECT_EQ(is_enabled, exp_val);
  }
}

TEST_F(WakeupRecording, GetReasonBadArgs) {
  dif_pwrmgr_wakeup_reason_t wakeup_reason;

  EXPECT_EQ(dif_pwrmgr_wakeup_reason_get(nullptr, &wakeup_reason),
            kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_wakeup_reason_get(&pwrmgr_, nullptr), kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_wakeup_reason_get(nullptr, nullptr), kDifPwrmgrBadArg);
}

/**
 * Custom equality matcher for `dif_pwrmgr_wakeup_reason_t`s.
 */
testing::Matcher<dif_pwrmgr_wakeup_reason_t> Eq(
    const dif_pwrmgr_wakeup_reason_t &rhs) {
  return testing::AllOf(
      testing::Field("types", &dif_pwrmgr_wakeup_reason_t::types, rhs.types),
      testing::Field("request_sources",
                     &dif_pwrmgr_wakeup_reason_t::request_sources,
                     rhs.request_sources));
}

TEST_F(WakeupRecording, GetReason) {
  struct TestCase {
    /**
     * Value that will be read from hardware.
     */
    std::initializer_list<mock_mmio::BitField> read_val;
    /**
     * Expected output.
     */
    dif_pwrmgr_wakeup_reason_t exp_output;
  };

  std::array<TestCase, 5> test_cases = {{
      // No bits set.
      {
          .read_val = {{
              .offset = 0,
              .value = 0,
          }},
          .exp_output =
              {
                  .types = 0,
                  .request_sources = 0,
              },
      },
      // All bits set.
      {
          .read_val = {{
                           .offset = PWRMGR_WAKE_INFO_ABORT_BIT,
                           .value = 1,
                       },
                       {
                           .offset = PWRMGR_WAKE_INFO_FALL_THROUGH_BIT,
                           .value = 1,
                       },
                       {
                           .offset = PWRMGR_WAKE_INFO_REASONS_BIT,
                           .value = 1,
                       }},
          .exp_output =
              {
                  .types = kDifPwrmgrWakeupTypeAbort |
                           kDifPwrmgrWakeupTypeFallThrough |
                           kDifPwrmgrWakeupTypeRequest,
                  .request_sources = kDifPwrmgrWakeupRequestSourceOne,
              },
      },
      // Only abort.
      {
          .read_val = {{
              .offset = PWRMGR_WAKE_INFO_ABORT_BIT,
              .value = 1,
          }},
          .exp_output =
              {
                  .types = kDifPwrmgrWakeupTypeAbort,
                  .request_sources = 0,
              },
      },
      // Only fall-through.
      {
          .read_val = {{
              .offset = PWRMGR_WAKE_INFO_FALL_THROUGH_BIT,
              .value = 1,
          }},
          .exp_output =
              {
                  .types = kDifPwrmgrWakeupTypeFallThrough,
                  .request_sources = 0,
              },
      },
      // Only requests from peripherals.
      {
          .read_val = {{
              .offset = PWRMGR_WAKE_INFO_REASONS_BIT,
              .value = 1,
          }},
          .exp_output =
              {
                  .types = kDifPwrmgrWakeupTypeRequest,
                  .request_sources = kDifPwrmgrWakeupRequestSourceOne,
              },
      },
  }};

  for (const auto &test_case : test_cases) {
    EXPECT_READ32(PWRMGR_WAKE_INFO_REG_OFFSET, test_case.read_val);

    dif_pwrmgr_wakeup_reason_t wakeup_reason;
    EXPECT_EQ(dif_pwrmgr_wakeup_reason_get(&pwrmgr_, &wakeup_reason),
              kDifPwrmgrOk);
    EXPECT_THAT(wakeup_reason, Eq(test_case.exp_output));
  }
}

TEST_F(WakeupRecording, ClearReasonBadArgs) {
  EXPECT_EQ(dif_pwrmgr_wakeup_reason_clear(nullptr), kDifPwrmgrBadArg);
}

TEST_F(WakeupRecording, ClearReason) {
  EXPECT_WRITE32(PWRMGR_WAKE_INFO_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());

  EXPECT_EQ(dif_pwrmgr_wakeup_reason_clear(&pwrmgr_), kDifPwrmgrOk);
}

class IrqTest : public DifPwrmgrInitialized {};

TEST_F(IrqTest, IsPendingBadArgs) {
  bool is_pending;

  EXPECT_EQ(
      dif_pwrmgr_irq_is_pending(nullptr, kDifPwrmgrIrqWakeup, &is_pending),
      kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_irq_is_pending(&pwrmgr_, kBadIrq, &is_pending),
            kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_irq_is_pending(&pwrmgr_, kDifPwrmgrIrqWakeup, nullptr),
            kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_irq_is_pending(nullptr, kBadIrq, &is_pending),
            kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_irq_is_pending(nullptr, kDifPwrmgrIrqWakeup, nullptr),
            kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_irq_is_pending(&pwrmgr_, kBadIrq, nullptr),
            kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_irq_is_pending(nullptr, kBadIrq, nullptr),
            kDifPwrmgrBadArg);
}

TEST_F(IrqTest, IsPending) {
  for (std::underlying_type<dif_pwrmgr_irq_t>::type irq = 0;
       irq <= kDifPwrmgrIrqLast; ++irq) {
    for (auto exp_val : kAllBools) {
      EXPECT_READ32(PWRMGR_INTR_STATE_REG_OFFSET, {{
                                                      .offset = irq,
                                                      .value = exp_val,
                                                  }});

      bool is_pending = !exp_val;
      EXPECT_EQ(dif_pwrmgr_irq_is_pending(
                    &pwrmgr_, static_cast<dif_pwrmgr_irq_t>(irq), &is_pending),
                kDifPwrmgrOk);
      EXPECT_EQ(is_pending, exp_val);
    }
  }
}

TEST_F(IrqTest, AckBadArgs) {
  EXPECT_EQ(dif_pwrmgr_irq_acknowledge(nullptr, kDifPwrmgrIrqWakeup),
            kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_irq_acknowledge(&pwrmgr_, kBadIrq), kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_irq_acknowledge(nullptr, kBadIrq), kDifPwrmgrBadArg);
}

TEST_F(IrqTest, Ack) {
  for (std::underlying_type<dif_pwrmgr_irq_t>::type irq = 0;
       irq <= kDifPwrmgrIrqLast; ++irq) {
    EXPECT_WRITE32(PWRMGR_INTR_STATE_REG_OFFSET, (1u << irq));

    EXPECT_EQ(dif_pwrmgr_irq_acknowledge(&pwrmgr_,
                                         static_cast<dif_pwrmgr_irq_t>(irq)),
              kDifPwrmgrOk);
  }
}

TEST_F(IrqTest, GetEnabledBadArgs) {
  dif_pwrmgr_toggle_t is_enabled;

  EXPECT_EQ(
      dif_pwrmgr_irq_get_enabled(nullptr, kDifPwrmgrIrqWakeup, &is_enabled),
      kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_irq_get_enabled(&pwrmgr_, kBadIrq, &is_enabled),
            kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_irq_get_enabled(&pwrmgr_, kDifPwrmgrIrqWakeup, nullptr),
            kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_irq_get_enabled(nullptr, kBadIrq, &is_enabled),
            kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_irq_get_enabled(nullptr, kDifPwrmgrIrqWakeup, nullptr),
            kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_irq_get_enabled(&pwrmgr_, kBadIrq, nullptr),
            kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_irq_get_enabled(nullptr, kBadIrq, nullptr),
            kDifPwrmgrBadArg);
}

TEST_F(IrqTest, GetEnabled) {
  for (std::underlying_type<dif_pwrmgr_irq_t>::type irq = 0;
       irq <= kDifPwrmgrIrqLast; ++irq) {
    for (auto exp_val : kAllToggles) {
      EXPECT_READ32(PWRMGR_INTR_ENABLE_REG_OFFSET,
                    {{
                        .offset = irq,
                        .value = (exp_val == kDifPwrmgrToggleEnabled),
                    }});

      dif_pwrmgr_toggle_t is_enabled = (exp_val == kDifPwrmgrToggleEnabled)
                                           ? kDifPwrmgrToggleDisabled
                                           : kDifPwrmgrToggleEnabled;
      EXPECT_EQ(dif_pwrmgr_irq_get_enabled(
                    &pwrmgr_, static_cast<dif_pwrmgr_irq_t>(irq), &is_enabled),
                kDifPwrmgrOk);
      EXPECT_EQ(is_enabled, exp_val);
    }
  }
}

TEST_F(IrqTest, SetEnabledBadArgs) {
  EXPECT_EQ(dif_pwrmgr_irq_set_enabled(nullptr, kDifPwrmgrIrqWakeup,
                                       kDifPwrmgrToggleEnabled),
            kDifPwrmgrBadArg);
  EXPECT_EQ(
      dif_pwrmgr_irq_set_enabled(&pwrmgr_, kBadIrq, kDifPwrmgrToggleEnabled),
      kDifPwrmgrBadArg);
  EXPECT_EQ(
      dif_pwrmgr_irq_set_enabled(&pwrmgr_, kDifPwrmgrIrqWakeup, kBadToggle),
      kDifPwrmgrBadArg);
  EXPECT_EQ(
      dif_pwrmgr_irq_set_enabled(nullptr, kBadIrq, kDifPwrmgrToggleEnabled),
      kDifPwrmgrBadArg);
  EXPECT_EQ(
      dif_pwrmgr_irq_set_enabled(nullptr, kDifPwrmgrIrqWakeup, kBadToggle),
      kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_irq_set_enabled(&pwrmgr_, kBadIrq, kBadToggle),
            kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_irq_set_enabled(nullptr, kBadIrq, kBadToggle),
            kDifPwrmgrBadArg);
}

TEST_F(IrqTest, SetEnabled) {
  for (std::underlying_type<dif_pwrmgr_irq_t>::type irq = 0;
       irq <= kDifPwrmgrIrqLast; ++irq) {
    for (auto new_state : kAllToggles) {
      EXPECT_MASK32(PWRMGR_INTR_ENABLE_REG_OFFSET,
                    {{
                        .offset = irq,
                        .mask = 1,
                        .value = (new_state == kDifPwrmgrToggleEnabled),
                    }});

      EXPECT_EQ(dif_pwrmgr_irq_set_enabled(
                    &pwrmgr_, static_cast<dif_pwrmgr_irq_t>(irq), new_state),
                kDifPwrmgrOk);
    }
  }
}

TEST_F(IrqTest, ForceBadArgs) {
  EXPECT_EQ(dif_pwrmgr_irq_force(nullptr, kDifPwrmgrIrqWakeup),
            kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_irq_force(&pwrmgr_, kBadIrq), kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_irq_force(nullptr, kBadIrq), kDifPwrmgrBadArg);
}

TEST_F(IrqTest, Force) {
  for (std::underlying_type<dif_pwrmgr_irq_t>::type irq = 0;
       irq <= kDifPwrmgrIrqLast; ++irq) {
    EXPECT_WRITE32(PWRMGR_INTR_TEST_REG_OFFSET, {{
                                                    .offset = irq,
                                                    .value = 1,
                                                }});

    EXPECT_EQ(
        dif_pwrmgr_irq_force(&pwrmgr_, static_cast<dif_pwrmgr_irq_t>(irq)),
        kDifPwrmgrOk);
  }
}

TEST_F(IrqTest, DisableAllBadArgs) {
  dif_pwrmgr_irq_snapshot_t snapshot;

  // `snapshot` is optional.
  EXPECT_EQ(dif_pwrmgr_irq_disable_all(nullptr, &snapshot), kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_irq_disable_all(nullptr, nullptr), kDifPwrmgrBadArg);
}
TEST_F(IrqTest, DisableAll) {
  uint32_t exp_snapshot = 0xA5A5A5A5;

  // With `snapshot`.
  EXPECT_READ32(PWRMGR_INTR_ENABLE_REG_OFFSET, exp_snapshot);
  EXPECT_WRITE32(PWRMGR_INTR_ENABLE_REG_OFFSET, 0);

  dif_pwrmgr_irq_snapshot_t act_snapshot = 0;
  EXPECT_EQ(dif_pwrmgr_irq_disable_all(&pwrmgr_, &act_snapshot), kDifPwrmgrOk);
  EXPECT_EQ(act_snapshot, exp_snapshot);

  // Without `snapshot`.
  EXPECT_WRITE32(PWRMGR_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_pwrmgr_irq_disable_all(&pwrmgr_, nullptr), kDifPwrmgrOk);
}

TEST_F(IrqTest, RestoreAllBadArgs) {
  dif_pwrmgr_irq_snapshot_t snapshot;

  EXPECT_EQ(dif_pwrmgr_irq_restore_all(nullptr, &snapshot), kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_irq_restore_all(&pwrmgr_, nullptr), kDifPwrmgrBadArg);
  EXPECT_EQ(dif_pwrmgr_irq_restore_all(nullptr, nullptr), kDifPwrmgrBadArg);
}

TEST_F(IrqTest, RestoreAll) {
  dif_pwrmgr_irq_snapshot_t snapshot = 0xA5A5A5A5;

  EXPECT_WRITE32(PWRMGR_INTR_ENABLE_REG_OFFSET, snapshot);

  EXPECT_EQ(dif_pwrmgr_irq_restore_all(&pwrmgr_, &snapshot), kDifPwrmgrOk);
}

}  // namespace
}  // namespace dif_pwrmgr_unittest
