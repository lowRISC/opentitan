// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_pwrmgr.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"
#include "sw/device/lib/dif/dif_base.h"

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
static constexpr std::array<dif_toggle_t, 2> kAllToggles = {
    kDifToggleDisabled,
    kDifToggleEnabled,
};
static constexpr std::array<bool, 2> kAllBools = {true, false};
static constexpr dif_toggle_t kBadToggle = static_cast<dif_toggle_t>(2);
static constexpr dif_pwrmgr_req_type_t kBadReqType =
    static_cast<dif_pwrmgr_req_type_t>(kDifPwrmgrReqTypeReset + 1);
static constexpr dif_pwrmgr_domain_config_t kBadConfig =
    std::numeric_limits<uint8_t>::max();
static constexpr dif_pwrmgr_request_sources_t kBadSources =
    std::numeric_limits<uint32_t>::max();

// Base class for the rest of the tests in this file, provides a
// `dif_pwrmgr_t` instance.
class DifPwrmgrInitialized : public testing::Test, public mock_mmio::MmioTest {
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
  const dif_pwrmgr_t pwrmgr_ = {.base_addr = dev().region()};
};

class LowPowerTest : public DifPwrmgrInitialized {};

TEST_F(LowPowerTest, SetBadArgs) {
  EXPECT_EQ(dif_pwrmgr_low_power_set_enabled(nullptr, kDifToggleEnabled,
                                             kDifToggleEnabled),
            kDifBadArg);
  EXPECT_EQ(
      dif_pwrmgr_low_power_set_enabled(&pwrmgr_, kBadToggle, kDifToggleEnabled),
      kDifBadArg);
  EXPECT_EQ(
      dif_pwrmgr_low_power_set_enabled(&pwrmgr_, kDifToggleEnabled, kBadToggle),
      kDifBadArg);
  EXPECT_EQ(
      dif_pwrmgr_low_power_set_enabled(nullptr, kBadToggle, kDifToggleEnabled),
      kDifBadArg);
  EXPECT_EQ(
      dif_pwrmgr_low_power_set_enabled(nullptr, kDifToggleEnabled, kBadToggle),
      kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_low_power_set_enabled(&pwrmgr_, kBadToggle, kBadToggle),
            kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_low_power_set_enabled(nullptr, kBadToggle, kBadToggle),
            kDifBadArg);
}

TEST_F(LowPowerTest, SetLocked) {
  for (auto new_toggle : kAllToggles) {
    for (auto sync_toggle : kAllToggles) {
      EXPECT_READ32(PWRMGR_CTRL_CFG_REGWEN_REG_OFFSET,
                    AllOnesExcept(PWRMGR_CTRL_CFG_REGWEN_EN_BIT));

      EXPECT_EQ(
          dif_pwrmgr_low_power_set_enabled(&pwrmgr_, new_toggle, sync_toggle),
          kDifLocked);
    }
  }
}

TEST_F(LowPowerTest, Set) {
  for (auto new_toggle : kAllToggles) {
    for (auto sync_toggle : kAllToggles) {
      EXPECT_READ32(PWRMGR_CTRL_CFG_REGWEN_REG_OFFSET,
                    {{
                        .offset = PWRMGR_CTRL_CFG_REGWEN_EN_BIT,
                        .value = 1,
                    }});
      EXPECT_MASK32(PWRMGR_CONTROL_REG_OFFSET,
                    {{
                        .offset = PWRMGR_CONTROL_LOW_POWER_HINT_BIT,
                        .mask = 1,
                        .value = (new_toggle == kDifToggleEnabled),
                    }});
      if (sync_toggle == kDifToggleEnabled)
        ExpectSync();

      EXPECT_EQ(
          dif_pwrmgr_low_power_set_enabled(&pwrmgr_, new_toggle, sync_toggle),
          kDifOk);
    }
  }
}

TEST_F(LowPowerTest, GetBadArgs) {
  dif_toggle_t state;

  EXPECT_EQ(dif_pwrmgr_low_power_get_enabled(nullptr, &state), kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_low_power_get_enabled(&pwrmgr_, nullptr), kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_low_power_get_enabled(nullptr, nullptr), kDifBadArg);
}

TEST_F(LowPowerTest, Get) {
  for (auto toggle : kAllToggles) {
    dif_toggle_t state;

    EXPECT_READ32(PWRMGR_CONTROL_REG_OFFSET,
                  {{
                      .offset = PWRMGR_CONTROL_LOW_POWER_HINT_BIT,
                      .value = (toggle == kDifToggleEnabled),
                  }});

    EXPECT_EQ(dif_pwrmgr_low_power_get_enabled(&pwrmgr_, &state), kDifOk);
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
  EXPECT_EQ(dif_pwrmgr_set_domain_config(nullptr, 0, kDifToggleEnabled),
            kDifBadArg);
  EXPECT_EQ(
      dif_pwrmgr_set_domain_config(&pwrmgr_, kBadConfig, kDifToggleEnabled),
      kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_set_domain_config(&pwrmgr_, 0, kBadToggle), kDifBadArg);
  EXPECT_EQ(
      dif_pwrmgr_set_domain_config(nullptr, kBadConfig, kDifToggleEnabled),
      kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_set_domain_config(nullptr, 0, kBadToggle), kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_set_domain_config(&pwrmgr_, kBadConfig, kBadToggle),
            kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_set_domain_config(nullptr, kBadConfig, kBadToggle),
            kDifBadArg);
}

TEST_F(DomainConfig, SetLocked) {
  EXPECT_READ32(PWRMGR_CTRL_CFG_REGWEN_REG_OFFSET,
                AllOnesExcept(PWRMGR_WAKEUP_EN_REGWEN_EN_BIT));

  EXPECT_EQ(dif_pwrmgr_set_domain_config(&pwrmgr_, 0, kDifToggleEnabled),
            kDifLocked);
}

TEST_F(DomainConfig, Set) {
  for (auto config : kConfigs) {
    for (auto toggle : kAllToggles) {
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
      if (toggle == kDifToggleEnabled)
        ExpectSync();

      EXPECT_EQ(dif_pwrmgr_set_domain_config(&pwrmgr_, config, toggle), kDifOk);
    }
  }
}

TEST_F(DomainConfig, GetBadArgs) {
  dif_pwrmgr_domain_config_t config;
  EXPECT_EQ(dif_pwrmgr_get_domain_config(nullptr, &config), kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_get_domain_config(&pwrmgr_, nullptr), kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_get_domain_config(nullptr, nullptr), kDifBadArg);
}

TEST_F(DomainConfig, Get) {
  for (auto exp_config : kConfigs) {
    EXPECT_READ32(PWRMGR_CONTROL_REG_OFFSET,
                  {{
                      .offset = kConfigBitfield.index,
                      .value = exp_config,
                  }});

    dif_pwrmgr_domain_config_t act_config;
    EXPECT_EQ(dif_pwrmgr_get_domain_config(&pwrmgr_, &act_config), kDifOk);
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
                                           kDifPwrmgrWakeupRequestSourceOne,
                                           kDifToggleEnabled),
            kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_set_request_sources(&pwrmgr_, kBadReqType,
                                           kDifPwrmgrWakeupRequestSourceOne,
                                           kDifToggleEnabled),
            kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_set_request_sources(&pwrmgr_, kDifPwrmgrReqTypeWakeup,
                                           kBadSources, kDifToggleEnabled),
            kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_set_request_sources(&pwrmgr_, kDifPwrmgrReqTypeWakeup,
                                           kDifPwrmgrWakeupRequestSourceOne,
                                           kBadToggle),
            kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_set_request_sources(nullptr, kBadReqType,
                                           kDifPwrmgrWakeupRequestSourceOne,
                                           kDifToggleEnabled),
            kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_set_request_sources(nullptr, kDifPwrmgrReqTypeWakeup,
                                           kBadSources, kDifToggleEnabled),
            kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_set_request_sources(nullptr, kDifPwrmgrReqTypeWakeup,
                                           kDifPwrmgrWakeupRequestSourceOne,
                                           kBadToggle),
            kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_set_request_sources(&pwrmgr_, kBadReqType, kBadSources,
                                           kDifToggleEnabled),
            kDifBadArg);
  EXPECT_EQ(
      dif_pwrmgr_set_request_sources(
          &pwrmgr_, kBadReqType, kDifPwrmgrWakeupRequestSourceOne, kBadToggle),
      kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_set_request_sources(&pwrmgr_, kDifPwrmgrReqTypeWakeup,
                                           kBadSources, kBadToggle),
            kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_set_request_sources(nullptr, kBadReqType, kBadSources,
                                           kDifToggleEnabled),
            kDifBadArg);
  EXPECT_EQ(
      dif_pwrmgr_set_request_sources(
          nullptr, kBadReqType, kDifPwrmgrWakeupRequestSourceOne, kBadToggle),
      kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_set_request_sources(nullptr, kDifPwrmgrReqTypeWakeup,
                                           kBadSources, kBadToggle),
            kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_set_request_sources(&pwrmgr_, kBadReqType, kBadSources,
                                           kBadToggle),
            kDifBadArg);

  EXPECT_EQ(dif_pwrmgr_set_request_sources(nullptr, kBadReqType, kBadSources,
                                           kBadToggle),
            kDifBadArg);
}

TEST_F(RequestSources, SetWakeupLocked) {
  EXPECT_READ32(PWRMGR_WAKEUP_EN_REGWEN_REG_OFFSET,
                AllOnesExcept(PWRMGR_WAKEUP_EN_REGWEN_EN_BIT));

  EXPECT_EQ(dif_pwrmgr_set_request_sources(&pwrmgr_, kDifPwrmgrReqTypeWakeup,
                                           kDifPwrmgrWakeupRequestSourceOne,
                                           kDifToggleEnabled),
            kDifLocked);
}

TEST_F(RequestSources, SetResetLocked) {
  EXPECT_READ32(PWRMGR_RESET_EN_REGWEN_REG_OFFSET,
                AllOnesExcept(PWRMGR_RESET_EN_REGWEN_EN_BIT));

  EXPECT_EQ(dif_pwrmgr_set_request_sources(&pwrmgr_, kDifPwrmgrReqTypeReset,
                                           kDifPwrmgrResetRequestSourceOne,
                                           kDifToggleEnabled),
            kDifLocked);
}

TEST_F(RequestSources, SetWakeup) {
  for (auto toggle : kAllToggles) {
    EXPECT_READ32(PWRMGR_WAKEUP_EN_REGWEN_REG_OFFSET,
                  {{
                      .offset = PWRMGR_WAKEUP_EN_REGWEN_EN_BIT,
                      .value = 1,
                  }});
    EXPECT_WRITE32(PWRMGR_WAKEUP_EN_REG_OFFSET,
                   kDifPwrmgrWakeupRequestSourceOne);
    if (toggle == kDifToggleEnabled)
      ExpectSync();

    EXPECT_EQ(dif_pwrmgr_set_request_sources(&pwrmgr_, kDifPwrmgrReqTypeWakeup,
                                             kDifPwrmgrWakeupRequestSourceOne,
                                             toggle),
              kDifOk);
  }
}

TEST_F(RequestSources, SetReset) {
  for (auto toggle : kAllToggles) {
    EXPECT_READ32(PWRMGR_RESET_EN_REGWEN_REG_OFFSET,
                  {{
                      .offset = PWRMGR_RESET_EN_REGWEN_EN_BIT,
                      .value = 1,
                  }});
    EXPECT_WRITE32(PWRMGR_RESET_EN_REG_OFFSET, kDifPwrmgrResetRequestSourceOne);
    if (toggle == kDifToggleEnabled)
      ExpectSync();

    EXPECT_EQ(
        dif_pwrmgr_set_request_sources(&pwrmgr_, kDifPwrmgrReqTypeReset,
                                       kDifPwrmgrResetRequestSourceOne, toggle),
        kDifOk);
  }
}

TEST_F(RequestSources, GetBadArgs) {
  dif_pwrmgr_request_sources_t sources;

  EXPECT_EQ(dif_pwrmgr_get_request_sources(nullptr, kDifPwrmgrReqTypeWakeup,
                                           &sources),
            kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_get_request_sources(&pwrmgr_, kBadReqType, &sources),
            kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_get_request_sources(&pwrmgr_, kDifPwrmgrReqTypeWakeup,
                                           nullptr),
            kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_get_request_sources(nullptr, kBadReqType, &sources),
            kDifBadArg);
  EXPECT_EQ(
      dif_pwrmgr_get_request_sources(nullptr, kDifPwrmgrReqTypeWakeup, nullptr),
      kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_get_request_sources(&pwrmgr_, kBadReqType, nullptr),
            kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_get_request_sources(nullptr, kBadReqType, nullptr),
            kDifBadArg);
}

TEST_F(RequestSources, GetWakeup) {
  for (auto exp_sources : kWakeupSources) {
    EXPECT_READ32(PWRMGR_WAKEUP_EN_REG_OFFSET, exp_sources);

    dif_pwrmgr_request_sources_t act_sources = 0;
    EXPECT_EQ(dif_pwrmgr_get_request_sources(&pwrmgr_, kDifPwrmgrReqTypeWakeup,
                                             &act_sources),
              kDifOk);
    EXPECT_EQ(act_sources, exp_sources);
  }
}

TEST_F(RequestSources, GetReset) {
  for (auto exp_sources : kResetSources) {
    EXPECT_READ32(PWRMGR_RESET_EN_REG_OFFSET, exp_sources);

    dif_pwrmgr_request_sources_t act_sources = 0;
    EXPECT_EQ(dif_pwrmgr_get_request_sources(&pwrmgr_, kDifPwrmgrReqTypeReset,
                                             &act_sources),
              kDifOk);
    EXPECT_EQ(act_sources, exp_sources);
  }
}

TEST_F(RequestSources, GetCurrentBadArgs) {
  dif_pwrmgr_request_sources_t sources;

  EXPECT_EQ(dif_pwrmgr_get_current_request_sources(
                nullptr, kDifPwrmgrReqTypeWakeup, &sources),
            kDifBadArg);
  EXPECT_EQ(
      dif_pwrmgr_get_current_request_sources(&pwrmgr_, kBadReqType, &sources),
      kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_get_current_request_sources(
                &pwrmgr_, kDifPwrmgrReqTypeWakeup, nullptr),
            kDifBadArg);
  EXPECT_EQ(
      dif_pwrmgr_get_current_request_sources(nullptr, kBadReqType, &sources),
      kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_get_current_request_sources(
                nullptr, kDifPwrmgrReqTypeWakeup, nullptr),
            kDifBadArg);
  EXPECT_EQ(
      dif_pwrmgr_get_current_request_sources(&pwrmgr_, kBadReqType, nullptr),
      kDifBadArg);
  EXPECT_EQ(
      dif_pwrmgr_get_current_request_sources(nullptr, kBadReqType, nullptr),
      kDifBadArg);
}

TEST_F(RequestSources, GetCurrentWakeup) {
  for (auto exp_sources : kWakeupSources) {
    EXPECT_READ32(PWRMGR_WAKE_STATUS_REG_OFFSET, exp_sources);

    dif_pwrmgr_request_sources_t act_sources = 0;
    EXPECT_EQ(dif_pwrmgr_get_current_request_sources(
                  &pwrmgr_, kDifPwrmgrReqTypeWakeup, &act_sources),
              kDifOk);
    EXPECT_EQ(act_sources, exp_sources);
  }
}

TEST_F(RequestSources, GetCurrentReset) {
  for (auto exp_sources : kResetSources) {
    EXPECT_READ32(PWRMGR_RESET_STATUS_REG_OFFSET, exp_sources);

    dif_pwrmgr_request_sources_t act_sources = 0;
    EXPECT_EQ(dif_pwrmgr_get_current_request_sources(
                  &pwrmgr_, kDifPwrmgrReqTypeReset, &act_sources),
              kDifOk);
    EXPECT_EQ(act_sources, exp_sources);
  }
}

TEST_F(RequestSources, LockBadArgs) {
  EXPECT_EQ(dif_pwrmgr_request_sources_lock(nullptr, kDifPwrmgrReqTypeWakeup),
            kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_request_sources_lock(&pwrmgr_, kBadReqType), kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_request_sources_lock(nullptr, kBadReqType), kDifBadArg);
}

TEST_F(RequestSources, LockWakeup) {
  EXPECT_WRITE32(PWRMGR_WAKEUP_EN_REGWEN_REG_OFFSET, 0);

  EXPECT_EQ(dif_pwrmgr_request_sources_lock(&pwrmgr_, kDifPwrmgrReqTypeWakeup),
            kDifOk);
}

TEST_F(RequestSources, LockReset) {
  EXPECT_WRITE32(PWRMGR_RESET_EN_REGWEN_REG_OFFSET, 0);

  EXPECT_EQ(dif_pwrmgr_request_sources_lock(&pwrmgr_, kDifPwrmgrReqTypeReset),
            kDifOk);
}

TEST_F(RequestSources, IsLockedBadArgs) {
  bool is_locked;

  EXPECT_EQ(dif_pwrmgr_request_sources_is_locked(
                nullptr, kDifPwrmgrReqTypeWakeup, &is_locked),
            kDifBadArg);
  EXPECT_EQ(
      dif_pwrmgr_request_sources_is_locked(&pwrmgr_, kBadReqType, &is_locked),
      kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_request_sources_is_locked(
                &pwrmgr_, kDifPwrmgrReqTypeWakeup, nullptr),
            kDifBadArg);
  EXPECT_EQ(
      dif_pwrmgr_request_sources_is_locked(nullptr, kBadReqType, &is_locked),
      kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_request_sources_is_locked(
                nullptr, kDifPwrmgrReqTypeWakeup, nullptr),
            kDifBadArg);
  EXPECT_EQ(
      dif_pwrmgr_request_sources_is_locked(&pwrmgr_, kBadReqType, nullptr),
      kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_request_sources_is_locked(nullptr, kBadReqType, nullptr),
            kDifBadArg);
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
              kDifOk);
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
              kDifOk);
    EXPECT_EQ(is_locked, exp_val);
  }
}

class WakeupRecording : public DifPwrmgrInitialized {};

TEST_F(WakeupRecording, SetEnabledBadArgs) {
  EXPECT_EQ(dif_pwrmgr_wakeup_request_recording_set_enabled(nullptr,
                                                            kDifToggleEnabled),
            kDifBadArg);
  EXPECT_EQ(
      dif_pwrmgr_wakeup_request_recording_set_enabled(&pwrmgr_, kBadToggle),
      kDifBadArg);
  EXPECT_EQ(
      dif_pwrmgr_wakeup_request_recording_set_enabled(nullptr, kBadToggle),
      kDifBadArg);
}

TEST_F(WakeupRecording, SetEnabled) {
  for (auto new_state : kAllToggles) {
    EXPECT_WRITE32(PWRMGR_WAKE_INFO_CAPTURE_DIS_REG_OFFSET,
                   {{
                       .offset = PWRMGR_WAKE_INFO_CAPTURE_DIS_VAL_BIT,
                       .value = (new_state == kDifToggleDisabled),
                   }});

    EXPECT_EQ(
        dif_pwrmgr_wakeup_request_recording_set_enabled(&pwrmgr_, new_state),
        kDifOk);
  }
}

TEST_F(WakeupRecording, GetEnabledBadArgs) {
  dif_toggle_t is_enabled;

  EXPECT_EQ(
      dif_pwrmgr_wakeup_request_recording_get_enabled(nullptr, &is_enabled),
      kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_wakeup_request_recording_get_enabled(&pwrmgr_, nullptr),
            kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_wakeup_request_recording_get_enabled(nullptr, nullptr),
            kDifBadArg);
}

TEST_F(WakeupRecording, GetEnabled) {
  for (auto exp_val : kAllToggles) {
    EXPECT_READ32(PWRMGR_WAKE_INFO_CAPTURE_DIS_REG_OFFSET,
                  {{
                      .offset = PWRMGR_WAKE_INFO_CAPTURE_DIS_VAL_BIT,
                      .value = (exp_val == kDifToggleDisabled),
                  }});

    dif_toggle_t is_enabled =
        (exp_val == kDifToggleEnabled) ? kDifToggleDisabled : kDifToggleEnabled;
    EXPECT_EQ(
        dif_pwrmgr_wakeup_request_recording_get_enabled(&pwrmgr_, &is_enabled),
        kDifOk);
    EXPECT_EQ(is_enabled, exp_val);
  }
}

TEST_F(WakeupRecording, GetReasonBadArgs) {
  dif_pwrmgr_wakeup_reason_t wakeup_reason;

  EXPECT_EQ(dif_pwrmgr_wakeup_reason_get(nullptr, &wakeup_reason), kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_wakeup_reason_get(&pwrmgr_, nullptr), kDifBadArg);
  EXPECT_EQ(dif_pwrmgr_wakeup_reason_get(nullptr, nullptr), kDifBadArg);
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

  std::array<TestCase, 10> test_cases = {{
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
                           .offset = PWRMGR_PARAM_SYSRST_CTRL_AON_WKUP_REQ_IDX,
                           .value = 1,
                       },
                       {
                           .offset = PWRMGR_PARAM_ADC_CTRL_AON_WKUP_REQ_IDX,
                           .value = 1,
                       },
                       {
                           .offset = PWRMGR_PARAM_PINMUX_AON_PIN_WKUP_REQ_IDX,
                           .value = 1,
                       },
                       {
                           .offset = PWRMGR_PARAM_PINMUX_AON_USB_WKUP_REQ_IDX,
                           .value = 1,
                       },
                       {
                           .offset = PWRMGR_PARAM_AON_TIMER_AON_WKUP_REQ_IDX,
                           .value = 1,
                       },
                       {
                           .offset = PWRMGR_PARAM_SENSOR_CTRL_WKUP_REQ_IDX,
                           .value = 1,
                       }},
          .exp_output = {.types = kDifPwrmgrWakeupTypeAbort |
                                  kDifPwrmgrWakeupTypeFallThrough |
                                  kDifPwrmgrWakeupTypeRequest,
                         .request_sources = kDifPwrmgrWakeupRequestSourceOne |
                                            kDifPwrmgrWakeupRequestSourceTwo |
                                            kDifPwrmgrWakeupRequestSourceThree |
                                            kDifPwrmgrWakeupRequestSourceFour |
                                            kDifPwrmgrWakeupRequestSourceFive |
                                            kDifPwrmgrWakeupRequestSourceSix},
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
              .offset = PWRMGR_PARAM_SYSRST_CTRL_AON_WKUP_REQ_IDX,
              .value = 1,
          }},
          .exp_output =
              {
                  .types = kDifPwrmgrWakeupTypeRequest,
                  .request_sources = kDifPwrmgrWakeupRequestSourceOne,
              },
      },
      {
          .read_val = {{
              .offset = PWRMGR_PARAM_ADC_CTRL_AON_WKUP_REQ_IDX,
              .value = 1,
          }},
          .exp_output =
              {
                  .types = kDifPwrmgrWakeupTypeRequest,
                  .request_sources = kDifPwrmgrWakeupRequestSourceTwo,
              },
      },
      {
          .read_val = {{
              .offset = PWRMGR_PARAM_PINMUX_AON_PIN_WKUP_REQ_IDX,
              .value = 1,
          }},
          .exp_output =
              {
                  .types = kDifPwrmgrWakeupTypeRequest,
                  .request_sources = kDifPwrmgrWakeupRequestSourceThree,
              },
      },
      {
          .read_val = {{
              .offset = PWRMGR_PARAM_PINMUX_AON_USB_WKUP_REQ_IDX,
              .value = 1,
          }},
          .exp_output =
              {
                  .types = kDifPwrmgrWakeupTypeRequest,
                  .request_sources = kDifPwrmgrWakeupRequestSourceFour,
              },
      },
      {
          .read_val = {{
              .offset = PWRMGR_PARAM_AON_TIMER_AON_WKUP_REQ_IDX,
              .value = 1,
          }},
          .exp_output =
              {
                  .types = kDifPwrmgrWakeupTypeRequest,
                  .request_sources = kDifPwrmgrWakeupRequestSourceFive,
              },
      },
      {
          .read_val = {{
              .offset = PWRMGR_PARAM_SENSOR_CTRL_WKUP_REQ_IDX,
              .value = 1,
          }},
          .exp_output =
              {
                  .types = kDifPwrmgrWakeupTypeRequest,
                  .request_sources = kDifPwrmgrWakeupRequestSourceSix,
              },
      },
  }};

  for (const auto &test_case : test_cases) {
    EXPECT_READ32(PWRMGR_WAKE_INFO_REG_OFFSET, test_case.read_val);

    dif_pwrmgr_wakeup_reason_t wakeup_reason;
    EXPECT_EQ(dif_pwrmgr_wakeup_reason_get(&pwrmgr_, &wakeup_reason), kDifOk);
    EXPECT_THAT(wakeup_reason, Eq(test_case.exp_output));
  }
}

TEST_F(WakeupRecording, ClearReasonBadArgs) {
  EXPECT_EQ(dif_pwrmgr_wakeup_reason_clear(nullptr), kDifBadArg);
}

TEST_F(WakeupRecording, ClearReason) {
  EXPECT_WRITE32(PWRMGR_WAKE_INFO_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());

  EXPECT_EQ(dif_pwrmgr_wakeup_reason_clear(&pwrmgr_), kDifOk);
}

}  // namespace
}  // namespace dif_pwrmgr_unittest
