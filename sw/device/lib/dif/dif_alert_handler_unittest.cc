// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_alert_handler.h"

#include <cstring>
#include <limits>
#include <ostream>

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"

#include "alert_handler_regs.h"  // Generated.

namespace dif_alert_handler_unittest {
namespace {
using ::mock_mmio::LeInt;
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::_;
using ::testing::Return;

constexpr uint32_t kAlerts = ALERT_HANDLER_PARAM_N_ALERTS;
constexpr uint32_t kAllZeros = 0;

class AlertHandlerTest : public testing::Test, public MmioTest {
 protected:
  dif_alert_handler_t alert_handler_ = {.base_addr = dev().region()};
};

class AlertConfigTest : public AlertHandlerTest,
                        public testing::WithParamInterface<
                            std::tuple<int, dif_alert_handler_class_t>> {};

TEST_F(AlertConfigTest, BadArgs) {
  EXPECT_EQ(dif_alert_handler_configure_alert(
                &alert_handler_, ALERT_HANDLER_PARAM_N_ALERTS,
                kDifAlertHandlerClassA, kDifToggleEnabled, kDifToggleDisabled),
            kDifBadArg);

  EXPECT_EQ(
      dif_alert_handler_configure_alert(
          &alert_handler_, 0,
          static_cast<dif_alert_handler_class_t>(ALERT_HANDLER_PARAM_N_CLASSES),
          kDifToggleEnabled, kDifToggleDisabled),
      kDifBadArg);

  EXPECT_EQ(dif_alert_handler_configure_alert(
                &alert_handler_, 0, kDifAlertHandlerClassA,
                static_cast<dif_toggle_t>(2), kDifToggleDisabled),
            kDifBadArg);

  EXPECT_EQ(dif_alert_handler_configure_alert(
                &alert_handler_, 0, kDifAlertHandlerClassA, kDifToggleEnabled,
                static_cast<dif_toggle_t>(2)),
            kDifBadArg);
}

TEST_F(AlertConfigTest, Locked) {
  EXPECT_READ32(ALERT_HANDLER_ALERT_REGWEN_0_REG_OFFSET, 0);
  EXPECT_EQ(dif_alert_handler_configure_alert(
                &alert_handler_, 0, kDifAlertHandlerClassA, kDifToggleEnabled,
                kDifToggleDisabled),
            kDifLocked);

  EXPECT_READ32(ALERT_HANDLER_ALERT_REGWEN_0_REG_OFFSET +
                    (ALERT_HANDLER_PARAM_N_ALERTS - 1) * sizeof(uint32_t),
                0);
  EXPECT_EQ(dif_alert_handler_configure_alert(
                &alert_handler_, ALERT_HANDLER_PARAM_N_ALERTS - 1,
                kDifAlertHandlerClassD, kDifToggleEnabled, kDifToggleEnabled),
            kDifLocked);
}

TEST_P(AlertConfigTest, EnableOnly) {
  dif_alert_handler_alert_t alert = std::get<0>(GetParam());
  dif_alert_handler_class_t alert_class = std::get<1>(GetParam());

  EXPECT_READ32(
      ALERT_HANDLER_ALERT_REGWEN_0_REG_OFFSET + alert * sizeof(uint32_t),
      ALERT_HANDLER_ALERT_REGWEN_0_REG_RESVAL);
  EXPECT_WRITE32_SHADOWED(
      ALERT_HANDLER_ALERT_EN_SHADOWED_0_REG_OFFSET + alert * sizeof(uint32_t),
      {{ALERT_HANDLER_ALERT_EN_SHADOWED_0_EN_A_0_BIT, true}});
  EXPECT_WRITE32_SHADOWED(
      ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_REG_OFFSET +
          alert * sizeof(uint32_t),
      {{ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_CLASS_A_0_OFFSET, alert_class}});

  EXPECT_EQ(
      dif_alert_handler_configure_alert(&alert_handler_, alert, alert_class,
                                        kDifToggleEnabled, kDifToggleDisabled),
      kDifOk);
}

TEST_P(AlertConfigTest, EnableAndLock) {
  dif_alert_handler_alert_t alert = std::get<0>(GetParam());
  dif_alert_handler_class_t alert_class = std::get<1>(GetParam());

  EXPECT_READ32(
      ALERT_HANDLER_ALERT_REGWEN_0_REG_OFFSET + alert * sizeof(uint32_t),
      ALERT_HANDLER_ALERT_REGWEN_0_REG_RESVAL);
  EXPECT_WRITE32_SHADOWED(
      ALERT_HANDLER_ALERT_EN_SHADOWED_0_REG_OFFSET + alert * sizeof(uint32_t),
      {{ALERT_HANDLER_ALERT_EN_SHADOWED_0_EN_A_0_BIT, true}});
  EXPECT_WRITE32_SHADOWED(
      ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_REG_OFFSET +
          alert * sizeof(uint32_t),
      {{ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_CLASS_A_0_OFFSET, alert_class}});
  EXPECT_WRITE32(
      ALERT_HANDLER_ALERT_REGWEN_0_REG_OFFSET + alert * sizeof(uint32_t), 0);

  EXPECT_EQ(
      dif_alert_handler_configure_alert(&alert_handler_, alert, alert_class,
                                        kDifToggleEnabled, kDifToggleEnabled),
      kDifOk);
}

INSTANTIATE_TEST_SUITE_P(
    AllAlertsAndClasses, AlertConfigTest,
    testing::Combine(testing::Range(0, ALERT_HANDLER_PARAM_N_ALERTS),
                     testing::Values(kDifAlertHandlerClassA,
                                     kDifAlertHandlerClassB,
                                     kDifAlertHandlerClassC,
                                     kDifAlertHandlerClassD)));

class LocalAlertConfigTest
    : public AlertHandlerTest,
      public testing::WithParamInterface<std::tuple<
          dif_alert_handler_local_alert_t, dif_alert_handler_class_t>> {};

TEST_F(LocalAlertConfigTest, BadArgs) {
  EXPECT_EQ(dif_alert_handler_configure_local_alert(
                &alert_handler_,
                static_cast<dif_alert_handler_local_alert_t>(
                    ALERT_HANDLER_PARAM_N_LOC_ALERT),
                kDifAlertHandlerClassA, kDifToggleEnabled, kDifToggleDisabled),
            kDifBadArg);

  EXPECT_EQ(
      dif_alert_handler_configure_local_alert(
          &alert_handler_, kDifAlertHandlerLocalAlertAlertPingFail,
          static_cast<dif_alert_handler_class_t>(ALERT_HANDLER_PARAM_N_CLASSES),
          kDifToggleEnabled, kDifToggleDisabled),
      kDifBadArg);

  EXPECT_EQ(dif_alert_handler_configure_local_alert(
                &alert_handler_, kDifAlertHandlerLocalAlertAlertPingFail,
                kDifAlertHandlerClassA, static_cast<dif_toggle_t>(2),
                kDifToggleDisabled),
            kDifBadArg);

  EXPECT_EQ(dif_alert_handler_configure_local_alert(
                &alert_handler_, kDifAlertHandlerLocalAlertAlertPingFail,
                kDifAlertHandlerClassA, kDifToggleEnabled,
                static_cast<dif_toggle_t>(2)),
            kDifBadArg);
}

TEST_F(LocalAlertConfigTest, Locked) {
  EXPECT_READ32(ALERT_HANDLER_LOC_ALERT_REGWEN_0_REG_OFFSET, 0);
  EXPECT_EQ(dif_alert_handler_configure_local_alert(
                &alert_handler_, kDifAlertHandlerLocalAlertAlertPingFail,
                kDifAlertHandlerClassA, kDifToggleEnabled, kDifToggleDisabled),
            kDifLocked);

  EXPECT_READ32(ALERT_HANDLER_LOC_ALERT_REGWEN_6_REG_OFFSET, 0);
  EXPECT_EQ(dif_alert_handler_configure_local_alert(
                &alert_handler_, kDifAlertHandlerLocalAlertShadowedStorageError,
                kDifAlertHandlerClassD, kDifToggleEnabled, kDifToggleEnabled),
            kDifLocked);
}

TEST_P(LocalAlertConfigTest, EnableOnly) {
  dif_alert_handler_local_alert_t local_alert = std::get<0>(GetParam());
  dif_alert_handler_class_t alert_class = std::get<1>(GetParam());

  EXPECT_READ32(ALERT_HANDLER_LOC_ALERT_REGWEN_0_REG_OFFSET +
                    static_cast<uint32_t>(local_alert) * sizeof(uint32_t),
                ALERT_HANDLER_LOC_ALERT_REGWEN_0_REG_RESVAL);
  EXPECT_WRITE32_SHADOWED(
      ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_0_REG_OFFSET +
          static_cast<uint32_t>(local_alert) * sizeof(uint32_t),
      {{ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_0_EN_LA_0_BIT, true}});
  EXPECT_WRITE32_SHADOWED(
      ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_REG_OFFSET +
          static_cast<uint32_t>(local_alert) * sizeof(uint32_t),
      {{ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_CLASS_LA_0_OFFSET,
        alert_class}});

  EXPECT_EQ(dif_alert_handler_configure_local_alert(
                &alert_handler_, local_alert, alert_class, kDifToggleEnabled,
                kDifToggleDisabled),
            kDifOk);
}

TEST_P(LocalAlertConfigTest, EnableAndLock) {
  dif_alert_handler_local_alert_t local_alert = std::get<0>(GetParam());
  dif_alert_handler_class_t alert_class = std::get<1>(GetParam());

  EXPECT_READ32(ALERT_HANDLER_LOC_ALERT_REGWEN_0_REG_OFFSET +
                    static_cast<uint32_t>(local_alert) * sizeof(uint32_t),
                ALERT_HANDLER_LOC_ALERT_REGWEN_0_REG_RESVAL);
  EXPECT_WRITE32_SHADOWED(
      ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_0_REG_OFFSET +
          static_cast<uint32_t>(local_alert) * sizeof(uint32_t),
      {{ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_0_EN_LA_0_BIT, true}});
  EXPECT_WRITE32_SHADOWED(
      ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_REG_OFFSET +
          static_cast<uint32_t>(local_alert) * sizeof(uint32_t),
      {{ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_CLASS_LA_0_OFFSET,
        alert_class}});
  EXPECT_WRITE32(ALERT_HANDLER_LOC_ALERT_REGWEN_0_REG_OFFSET +
                     static_cast<uint32_t>(local_alert) * sizeof(uint32_t),
                 0);

  EXPECT_EQ(dif_alert_handler_configure_local_alert(
                &alert_handler_, local_alert, alert_class, kDifToggleEnabled,
                kDifToggleEnabled),
            kDifOk);
}

INSTANTIATE_TEST_SUITE_P(
    AllLocalAlertsAndClasses, LocalAlertConfigTest,
    testing::Combine(
        testing::Values(kDifAlertHandlerLocalAlertAlertPingFail,
                        kDifAlertHandlerLocalAlertEscalationPingFail,
                        kDifAlertHandlerLocalAlertAlertIntegrityFail,
                        kDifAlertHandlerLocalAlertEscalationIntegrityFail,
                        kDifAlertHandlerLocalAlertBusIntegrityFail,
                        kDifAlertHandlerLocalAlertShadowedUpdateError,
                        kDifAlertHandlerLocalAlertShadowedStorageError),
        testing::Values(kDifAlertHandlerClassA, kDifAlertHandlerClassB,
                        kDifAlertHandlerClassC, kDifAlertHandlerClassD)));

class ConfigTest : public AlertHandlerTest {
  // We provide our own dev_ member variable in this fixture, in order to
  // support IgnoreMmioCalls().
  //
  // NOTE: This must come before alert_handler_!
 private:
  std::unique_ptr<MockDevice> dev_ =
      std::make_unique<testing::StrictMock<MockDevice>>();

 protected:
  ConfigTest() { alert_handler_.base_addr = dev().region(); }
  // Non-virtual-override dev(), so that EXPECT_*() functions look this one
  // up instead of AlertHandlerTest::dev().
  MockDevice &dev() { return *dev_; }

  // Disables expectations on MMIO operations. This is useful for configuration
  // tests that partially configure the device but fail due to a configuration
  // error, returning kDifError.
  void IgnoreMmioCalls() {
    dev_ = std::make_unique<testing::NiceMock<MockDevice>>();
    alert_handler_.base_addr = dev().region();

    // Make sure that the peripheral looks unlocked.
    ON_CALL(*dev_, Read32(_)).WillByDefault(Return(kAllZeros));
  }
};

TEST_F(ConfigTest, Locked) {
  dif_alert_handler_config_t config = {
      .ping_timeout = 0,
  };

  EXPECT_READ32(
      ALERT_HANDLER_PING_TIMER_EN_SHADOWED_REG_OFFSET,
      {{ALERT_HANDLER_PING_TIMER_EN_SHADOWED_PING_TIMER_EN_SHADOWED_BIT,
        true}});

  EXPECT_EQ(dif_alert_handler_configure(&alert_handler_, config), kDifLocked);
}

TEST_F(ConfigTest, NoClassInit) {
  dif_alert_handler_config_t config = {
      .ping_timeout = 50,
  };

  EXPECT_READ32(
      ALERT_HANDLER_PING_TIMER_EN_SHADOWED_REG_OFFSET,
      {{ALERT_HANDLER_PING_TIMER_EN_SHADOWED_PING_TIMER_EN_SHADOWED_BIT,
        false}});

  EXPECT_WRITE32_SHADOWED(
      ALERT_HANDLER_PING_TIMEOUT_CYC_SHADOWED_REG_OFFSET,
      {{ALERT_HANDLER_PING_TIMEOUT_CYC_SHADOWED_PING_TIMEOUT_CYC_SHADOWED_OFFSET,
        50}});

  EXPECT_EQ(dif_alert_handler_configure(&alert_handler_, config), kDifOk);
}

TEST_F(ConfigTest, TimeoutTooBig) {
  dif_alert_handler_config_t config = {
      .ping_timeout =
          ALERT_HANDLER_PING_TIMEOUT_CYC_SHADOWED_PING_TIMEOUT_CYC_SHADOWED_MASK +
          1,
  };

  EXPECT_EQ(dif_alert_handler_configure(&alert_handler_, config), kDifBadArg);
}

TEST_F(ConfigTest, BadClassPtr) {
  dif_alert_handler_config_t config = {
      .ping_timeout = 50,
      .classes = nullptr,
      .classes_len = 2,
  };

  EXPECT_EQ(dif_alert_handler_configure(&alert_handler_, config), kDifBadArg);
}

TEST_F(ConfigTest, ClassInit) {
  std::vector<dif_alert_handler_alert_t> alerts_a = {1, 2, 5};
  std::vector<dif_alert_handler_local_alert_t> locals_a = {
      kDifAlertHandlerLocalAlertEscalationPingFail,
  };
  std::vector<dif_alert_handler_class_phase_signal_t> signals_a = {
      {.phase = kDifAlertHandlerClassStatePhase0, .signal = 3},
      {.phase = kDifAlertHandlerClassStatePhase2, .signal = 1},
  };
  std::vector<dif_alert_handler_class_phase_duration_t> durations_a = {
      {.phase = kDifAlertHandlerClassStatePhase1, .cycles = 20000},
      {.phase = kDifAlertHandlerClassStatePhase2, .cycles = 15000},
  };

  std::vector<dif_alert_handler_alert_t> alerts_b = {9, 6, 11};
  std::vector<dif_alert_handler_local_alert_t> locals_b = {
      kDifAlertHandlerLocalAlertAlertPingFail,
      kDifAlertHandlerLocalAlertAlertIntegrityFail,
  };
  std::vector<dif_alert_handler_class_phase_signal_t> signals_b = {
      {.phase = kDifAlertHandlerClassStatePhase1, .signal = 0},
  };
  std::vector<dif_alert_handler_class_phase_duration_t> durations_b = {
      {.phase = kDifAlertHandlerClassStatePhase1, .cycles = 20000},
      {.phase = kDifAlertHandlerClassStatePhase2, .cycles = 15000},
      {.phase = kDifAlertHandlerClassStatePhase3, .cycles = 150000},
  };

  std::vector<dif_alert_handler_class_config_t> classes = {
      {
          .alert_class = kDifAlertHandlerClassA,
          .alerts = alerts_a.data(),
          .alerts_len = alerts_a.size(),
          .local_alerts = locals_a.data(),
          .local_alerts_len = locals_a.size(),
          .use_escalation_protocol = kDifToggleDisabled,
          .automatic_locking = kDifToggleEnabled,
          .accumulator_threshold = 12,
          .irq_deadline_cycles = 30000,
          .phase_signals = signals_a.data(),
          .phase_signals_len = signals_a.size(),
          .phase_durations = durations_a.data(),
          .phase_durations_len = durations_a.size(),
      },
      {
          .alert_class = kDifAlertHandlerClassB,
          .alerts = alerts_b.data(),
          .alerts_len = alerts_b.size(),
          .local_alerts = locals_b.data(),
          .local_alerts_len = locals_b.size(),
          .use_escalation_protocol = kDifToggleEnabled,
          .automatic_locking = kDifToggleDisabled,
          .accumulator_threshold = 8,
          .irq_deadline_cycles = 2000,
          .phase_signals = signals_b.data(),
          .phase_signals_len = signals_b.size(),
          .phase_durations = durations_b.data(),
          .phase_durations_len = durations_b.size(),
      },
  };

  dif_alert_handler_config_t config = {
      .ping_timeout = 50,
      .classes = classes.data(),
      .classes_len = classes.size(),
  };

  // Configure class A alerts.
  // Unfortunately, we can't use EXPECT_MASK for these reads/writes, since the
  // target registers are shadowed.
  for (auto alert : alerts_a) {
    // The various alerts should be unlocked.
    ptrdiff_t alert_regwen_offset =
        ALERT_HANDLER_ALERT_REGWEN_0_REG_OFFSET + alert * sizeof(uint32_t);
    EXPECT_READ32(alert_regwen_offset, ALERT_HANDLER_ALERT_REGWEN_0_REG_RESVAL);
    // The various alerts should be enabled.
    ptrdiff_t alert_enable_reg_offset =
        ALERT_HANDLER_ALERT_EN_SHADOWED_0_REG_OFFSET + alert * sizeof(uint32_t);
    EXPECT_WRITE32_SHADOWED(
        alert_enable_reg_offset,
        {{ALERT_HANDLER_ALERT_EN_SHADOWED_0_EN_A_0_BIT, true}});
    // The various alerts should be classified.
    ptrdiff_t alert_class_reg_offset =
        ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_REG_OFFSET +
        alert * sizeof(uint32_t);
    EXPECT_WRITE32_SHADOWED(
        alert_class_reg_offset,
        ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_CLASS_A_0_VALUE_CLASSA);
  }

  // Configure class A local alerts.
  // Unfortunately, we can't use EXPECT_MASK for these reads/writes, since the
  // target registers are shadowed.
  EXPECT_READ32(ALERT_HANDLER_LOC_ALERT_REGWEN_1_REG_OFFSET,
                ALERT_HANDLER_LOC_ALERT_REGWEN_1_REG_RESVAL);
  EXPECT_WRITE32_SHADOWED(
      ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_1_REG_OFFSET,
      {{ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_1_EN_LA_1_BIT, true}});
  EXPECT_WRITE32_SHADOWED(
      ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_1_REG_OFFSET,
      ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_CLASS_LA_0_VALUE_CLASSA);

  // Configure class A control register.
  EXPECT_WRITE32_SHADOWED(
      ALERT_HANDLER_CLASSA_CTRL_SHADOWED_REG_OFFSET,
      {
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_BIT, false},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_LOCK_BIT, true},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E0_BIT, true},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E0_OFFSET, 3},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E2_BIT, true},
          {ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E2_OFFSET, 1},
      });

  EXPECT_WRITE32_SHADOWED(ALERT_HANDLER_CLASSA_ACCUM_THRESH_SHADOWED_REG_OFFSET,
                          12);
  EXPECT_WRITE32_SHADOWED(ALERT_HANDLER_CLASSA_TIMEOUT_CYC_SHADOWED_REG_OFFSET,
                          30000);

  EXPECT_WRITE32_SHADOWED(ALERT_HANDLER_CLASSA_PHASE1_CYC_SHADOWED_REG_OFFSET,
                          20000);
  EXPECT_WRITE32_SHADOWED(ALERT_HANDLER_CLASSA_PHASE2_CYC_SHADOWED_REG_OFFSET,
                          15000);

  // Configure class B alerts.
  // Unfortunately, we can't use EXPECT_MASK for these reads/writes, since the
  // target registers are shadowed.
  for (auto alert : alerts_b) {
    // The various alerts should be unlocked.
    ptrdiff_t alert_regwen_offset =
        ALERT_HANDLER_ALERT_REGWEN_0_REG_OFFSET + alert * sizeof(uint32_t);
    EXPECT_READ32(alert_regwen_offset, ALERT_HANDLER_ALERT_REGWEN_0_REG_RESVAL);
    // The various alerts should be enabled.
    ptrdiff_t alert_enable_reg_offset =
        ALERT_HANDLER_ALERT_EN_SHADOWED_0_REG_OFFSET + alert * sizeof(uint32_t);
    EXPECT_WRITE32_SHADOWED(
        alert_enable_reg_offset,
        {{ALERT_HANDLER_ALERT_EN_SHADOWED_0_EN_A_0_BIT, true}});
    // The various alerts should be classified.
    ptrdiff_t alert_class_reg_offset =
        ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_REG_OFFSET +
        alert * sizeof(uint32_t);
    EXPECT_WRITE32_SHADOWED(
        alert_class_reg_offset,
        ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_CLASS_A_0_VALUE_CLASSB);
  }

  // Configure class B local alerts.
  // Unfortunately, we can't use EXPECT_MASK for these reads/writes, since the
  // target registers are shadowed.
  EXPECT_READ32(ALERT_HANDLER_LOC_ALERT_REGWEN_0_REG_OFFSET,
                ALERT_HANDLER_LOC_ALERT_REGWEN_0_REG_RESVAL);
  EXPECT_WRITE32_SHADOWED(
      ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_0_REG_OFFSET,
      {{ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_0_EN_LA_0_BIT, true}});
  EXPECT_WRITE32_SHADOWED(
      ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_REG_OFFSET,
      ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_CLASS_LA_0_VALUE_CLASSB);
  EXPECT_READ32(ALERT_HANDLER_LOC_ALERT_REGWEN_2_REG_OFFSET,
                ALERT_HANDLER_LOC_ALERT_REGWEN_2_REG_RESVAL);
  EXPECT_WRITE32_SHADOWED(
      ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_2_REG_OFFSET,
      {{ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_2_EN_LA_2_BIT, true}});
  EXPECT_WRITE32_SHADOWED(
      ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_2_REG_OFFSET,
      ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_CLASS_LA_0_VALUE_CLASSB);

  // Configure class B control register.
  EXPECT_WRITE32_SHADOWED(
      ALERT_HANDLER_CLASSB_CTRL_SHADOWED_REG_OFFSET,
      {
          {ALERT_HANDLER_CLASSB_CTRL_SHADOWED_EN_BIT, true},
          {ALERT_HANDLER_CLASSB_CTRL_SHADOWED_LOCK_BIT, false},
          {ALERT_HANDLER_CLASSB_CTRL_SHADOWED_EN_E1_BIT, true},
          {ALERT_HANDLER_CLASSB_CTRL_SHADOWED_MAP_E1_OFFSET, 0},
      });

  EXPECT_WRITE32_SHADOWED(ALERT_HANDLER_CLASSB_ACCUM_THRESH_SHADOWED_REG_OFFSET,
                          8);
  EXPECT_WRITE32_SHADOWED(ALERT_HANDLER_CLASSB_TIMEOUT_CYC_SHADOWED_REG_OFFSET,
                          2000);

  EXPECT_WRITE32_SHADOWED(ALERT_HANDLER_CLASSB_PHASE1_CYC_SHADOWED_REG_OFFSET,
                          20000);
  EXPECT_WRITE32_SHADOWED(ALERT_HANDLER_CLASSB_PHASE2_CYC_SHADOWED_REG_OFFSET,
                          15000);
  EXPECT_WRITE32_SHADOWED(ALERT_HANDLER_CLASSB_PHASE3_CYC_SHADOWED_REG_OFFSET,
                          150000);

  // The alert handler ping timer needs to be unlocked for it to be configured.
  EXPECT_READ32(
      ALERT_HANDLER_PING_TIMER_EN_SHADOWED_REG_OFFSET,
      {{ALERT_HANDLER_PING_TIMER_EN_SHADOWED_PING_TIMER_EN_SHADOWED_BIT,
        false}});

  EXPECT_WRITE32_SHADOWED(
      ALERT_HANDLER_PING_TIMEOUT_CYC_SHADOWED_REG_OFFSET,
      {{ALERT_HANDLER_PING_TIMEOUT_CYC_SHADOWED_PING_TIMEOUT_CYC_SHADOWED_OFFSET,
        50}});

  EXPECT_EQ(dif_alert_handler_configure(&alert_handler_, config), kDifOk);
}

TEST_F(ConfigTest, BadAlert) {
  IgnoreMmioCalls();

  std::vector<dif_alert_handler_alert_t> alerts_a = {1, 2, kAlerts + 1};
  std::vector<dif_alert_handler_local_alert_t> locals_a = {
      kDifAlertHandlerLocalAlertEscalationPingFail,
  };
  std::vector<dif_alert_handler_class_phase_signal_t> signals_a = {
      {.phase = kDifAlertHandlerClassStatePhase0, .signal = 3},
      {.phase = kDifAlertHandlerClassStatePhase2, .signal = 1},
  };
  std::vector<dif_alert_handler_class_phase_duration_t> durations_a = {
      {.phase = kDifAlertHandlerClassStatePhase1, .cycles = 20000},
      {.phase = kDifAlertHandlerClassStatePhase2, .cycles = 15000},
  };

  std::vector<dif_alert_handler_class_config_t> classes = {
      {
          .alert_class = kDifAlertHandlerClassA,
          .alerts = alerts_a.data(),
          .alerts_len = alerts_a.size(),
          .local_alerts = locals_a.data(),
          .local_alerts_len = locals_a.size(),
          .use_escalation_protocol = kDifToggleDisabled,
          .automatic_locking = kDifToggleEnabled,
          .accumulator_threshold = 12,
          .irq_deadline_cycles = 30000,
          .phase_signals = signals_a.data(),
          .phase_signals_len = signals_a.size(),
          .phase_durations = durations_a.data(),
          .phase_durations_len = durations_a.size(),
      },
  };

  dif_alert_handler_config_t config = {
      .ping_timeout = 50,
      .classes = classes.data(),
      .classes_len = classes.size(),
  };

  EXPECT_EQ(dif_alert_handler_configure(&alert_handler_, config), kDifError);
}

TEST_F(ConfigTest, BadSignalPhase) {
  IgnoreMmioCalls();

  std::vector<dif_alert_handler_alert_t> alerts_a = {1, 2, 5};
  std::vector<dif_alert_handler_local_alert_t> locals_a = {
      kDifAlertHandlerLocalAlertEscalationPingFail,
  };
  std::vector<dif_alert_handler_class_phase_signal_t> signals_a = {
      {.phase = kDifAlertHandlerClassStatePhase0, .signal = 3},
      {.phase = kDifAlertHandlerClassStateTerminal, .signal = 1},
  };
  std::vector<dif_alert_handler_class_phase_duration_t> durations_a = {
      {.phase = kDifAlertHandlerClassStatePhase1, .cycles = 20000},
      {.phase = kDifAlertHandlerClassStatePhase2, .cycles = 15000},
  };

  std::vector<dif_alert_handler_class_config_t> classes = {
      {
          .alert_class = kDifAlertHandlerClassA,
          .alerts = alerts_a.data(),
          .alerts_len = alerts_a.size(),
          .local_alerts = locals_a.data(),
          .local_alerts_len = locals_a.size(),
          .use_escalation_protocol = kDifToggleDisabled,
          .automatic_locking = kDifToggleEnabled,
          .accumulator_threshold = 12,
          .irq_deadline_cycles = 30000,
          .phase_signals = signals_a.data(),
          .phase_signals_len = signals_a.size(),
          .phase_durations = durations_a.data(),
          .phase_durations_len = durations_a.size(),
      },
  };

  dif_alert_handler_config_t config = {
      .ping_timeout = 50,
      .classes = classes.data(),
      .classes_len = classes.size(),
  };

  EXPECT_EQ(dif_alert_handler_configure(&alert_handler_, config), kDifError);
}

TEST_F(ConfigTest, BadDurationPhase) {
  IgnoreMmioCalls();

  std::vector<dif_alert_handler_alert_t> alerts_a = {1, 2, 5};
  std::vector<dif_alert_handler_local_alert_t> locals_a = {
      kDifAlertHandlerLocalAlertEscalationPingFail,
  };
  std::vector<dif_alert_handler_class_phase_signal_t> signals_a = {
      {.phase = kDifAlertHandlerClassStatePhase0, .signal = 3},
      {.phase = kDifAlertHandlerClassStatePhase2, .signal = 1},
  };
  std::vector<dif_alert_handler_class_phase_duration_t> durations_a = {
      {.phase = kDifAlertHandlerClassStateTerminal, .cycles = 20000},
      {.phase = kDifAlertHandlerClassStatePhase2, .cycles = 15000},
  };

  std::vector<dif_alert_handler_class_config_t> classes = {
      {
          .alert_class = kDifAlertHandlerClassA,
          .alerts = alerts_a.data(),
          .alerts_len = alerts_a.size(),
          .local_alerts = locals_a.data(),
          .local_alerts_len = locals_a.size(),
          .use_escalation_protocol = kDifToggleDisabled,
          .automatic_locking = kDifToggleEnabled,
          .accumulator_threshold = 12,
          .irq_deadline_cycles = 30000,
          .phase_signals = signals_a.data(),
          .phase_signals_len = signals_a.size(),
          .phase_durations = durations_a.data(),
          .phase_durations_len = durations_a.size(),
      },
  };

  dif_alert_handler_config_t config = {
      .ping_timeout = 50,
      .classes = classes.data(),
      .classes_len = classes.size(),
  };

  EXPECT_EQ(dif_alert_handler_configure(&alert_handler_, config), kDifError);
}

TEST_F(ConfigTest, BadPointers) {
  IgnoreMmioCalls();

  std::vector<dif_alert_handler_alert_t> alerts_a = {1, 2, 5};
  std::vector<dif_alert_handler_local_alert_t> locals_a = {
      kDifAlertHandlerLocalAlertEscalationPingFail,
  };
  std::vector<dif_alert_handler_class_phase_signal_t> signals_a = {
      {.phase = kDifAlertHandlerClassStatePhase0, .signal = 3},
      {.phase = kDifAlertHandlerClassStatePhase2, .signal = 1},
  };
  std::vector<dif_alert_handler_class_phase_duration_t> durations_a = {
      {.phase = kDifAlertHandlerClassStateTerminal, .cycles = 20000},
      {.phase = kDifAlertHandlerClassStatePhase2, .cycles = 15000},
  };

  std::vector<dif_alert_handler_class_config_t> classes = {
      {
          .alert_class = kDifAlertHandlerClassA,
          .alerts = alerts_a.data(),
          .alerts_len = alerts_a.size(),
          .local_alerts = locals_a.data(),
          .local_alerts_len = locals_a.size(),
          .use_escalation_protocol = kDifToggleDisabled,
          .automatic_locking = kDifToggleEnabled,
          .accumulator_threshold = 12,
          .irq_deadline_cycles = 30000,
          .phase_signals = signals_a.data(),
          .phase_signals_len = signals_a.size(),
          .phase_durations = durations_a.data(),
          .phase_durations_len = durations_a.size(),
      },
  };

  dif_alert_handler_config_t config = {
      .ping_timeout = 50,
      .classes = classes.data(),
      .classes_len = classes.size(),
  };

  classes[0].alerts = nullptr;
  EXPECT_EQ(dif_alert_handler_configure(&alert_handler_, config), kDifError);
  classes[0].alerts = alerts_a.data();

  classes[0].local_alerts = nullptr;
  EXPECT_EQ(dif_alert_handler_configure(&alert_handler_, config), kDifError);
  classes[0].local_alerts = locals_a.data();

  classes[0].phase_signals = nullptr;
  EXPECT_EQ(dif_alert_handler_configure(&alert_handler_, config), kDifError);
  classes[0].phase_signals = signals_a.data();

  classes[0].phase_durations = nullptr;
  EXPECT_EQ(dif_alert_handler_configure(&alert_handler_, config), kDifError);
}

TEST_F(ConfigTest, BadClass) {
  IgnoreMmioCalls();

  std::vector<dif_alert_handler_alert_t> alerts_a = {1, 2, 5};
  std::vector<dif_alert_handler_local_alert_t> locals_a = {
      kDifAlertHandlerLocalAlertEscalationPingFail,
  };
  std::vector<dif_alert_handler_class_phase_signal_t> signals_a = {
      {.phase = kDifAlertHandlerClassStatePhase0, .signal = 3},
      {.phase = kDifAlertHandlerClassStatePhase2, .signal = 1},
  };
  std::vector<dif_alert_handler_class_phase_duration_t> durations_a = {
      {.phase = kDifAlertHandlerClassStatePhase0, .cycles = 20000},
      {.phase = kDifAlertHandlerClassStatePhase2, .cycles = 15000},
  };

  std::vector<dif_alert_handler_class_config_t> classes = {
      {
          .alert_class = static_cast<dif_alert_handler_class_t>(12),
          .alerts = alerts_a.data(),
          .alerts_len = alerts_a.size(),
          .local_alerts = locals_a.data(),
          .local_alerts_len = locals_a.size(),
          .use_escalation_protocol = kDifToggleDisabled,
          .automatic_locking = kDifToggleEnabled,
          .accumulator_threshold = 12,
          .irq_deadline_cycles = 30000,
          .phase_signals = signals_a.data(),
          .phase_signals_len = signals_a.size(),
          .phase_durations = durations_a.data(),
          .phase_durations_len = durations_a.size(),
      },
  };

  dif_alert_handler_config_t config = {
      .ping_timeout = 50,
      .classes = classes.data(),
      .classes_len = classes.size(),
  };

  EXPECT_EQ(dif_alert_handler_configure(&alert_handler_, config), kDifError);
}

TEST_F(ConfigTest, NullArgs) {
  EXPECT_EQ(dif_alert_handler_configure(nullptr, {}), kDifBadArg);
}

class PingTimerLockTest : public AlertHandlerTest {};

TEST_F(PingTimerLockTest, IsPingTimerLocked) {
  bool flag;

  EXPECT_READ32(
      ALERT_HANDLER_PING_TIMER_EN_SHADOWED_REG_OFFSET,
      {{ALERT_HANDLER_PING_TIMER_EN_SHADOWED_PING_TIMER_EN_SHADOWED_BIT,
        false}});
  EXPECT_EQ(dif_alert_handler_is_ping_timer_locked(&alert_handler_, &flag),
            kDifOk);
  EXPECT_FALSE(flag);

  EXPECT_READ32(
      ALERT_HANDLER_PING_TIMER_EN_SHADOWED_REG_OFFSET,
      {{ALERT_HANDLER_PING_TIMER_EN_SHADOWED_PING_TIMER_EN_SHADOWED_BIT,
        true}});
  EXPECT_EQ(dif_alert_handler_is_ping_timer_locked(&alert_handler_, &flag),
            kDifOk);
  EXPECT_TRUE(flag);
}

TEST_F(PingTimerLockTest, LockPingTimer) {
  EXPECT_WRITE32_SHADOWED(
      ALERT_HANDLER_PING_TIMER_EN_SHADOWED_REG_OFFSET,
      {{ALERT_HANDLER_PING_TIMER_EN_SHADOWED_PING_TIMER_EN_SHADOWED_BIT,
        true}});
  EXPECT_EQ(dif_alert_handler_lock_ping_timer(&alert_handler_), kDifOk);
}

TEST_F(PingTimerLockTest, NullArgs) {
  bool flag;
  EXPECT_EQ(dif_alert_handler_is_ping_timer_locked(nullptr, &flag), kDifBadArg);
  EXPECT_EQ(dif_alert_handler_is_ping_timer_locked(&alert_handler_, nullptr),
            kDifBadArg);

  EXPECT_EQ(dif_alert_handler_lock_ping_timer(nullptr), kDifBadArg);
}

class CauseTest : public AlertHandlerTest {};

TEST_F(CauseTest, IsCause) {
  bool flag;

  EXPECT_READ32(ALERT_HANDLER_ALERT_CAUSE_5_REG_OFFSET, {{0, true}});
  EXPECT_EQ(dif_alert_handler_alert_is_cause(&alert_handler_, 5, &flag),
            kDifOk);
  EXPECT_TRUE(flag);

  EXPECT_READ32(ALERT_HANDLER_ALERT_CAUSE_6_REG_OFFSET, {{0, false}});
  EXPECT_EQ(dif_alert_handler_alert_is_cause(&alert_handler_, 6, &flag),
            kDifOk);
  EXPECT_FALSE(flag);
}

TEST_F(CauseTest, Ack) {
  EXPECT_WRITE32(ALERT_HANDLER_ALERT_CAUSE_0_REG_OFFSET,
                 {{ALERT_HANDLER_ALERT_CAUSE_0_A_0_BIT, true}});
  EXPECT_EQ(dif_alert_handler_alert_acknowledge(&alert_handler_, 0), kDifOk);

  EXPECT_WRITE32(ALERT_HANDLER_ALERT_CAUSE_11_REG_OFFSET,
                 {{ALERT_HANDLER_ALERT_CAUSE_11_A_11_BIT, true}});
  EXPECT_EQ(dif_alert_handler_alert_acknowledge(&alert_handler_, 11), kDifOk);
}

TEST_F(CauseTest, BadAlert) {
  bool flag;
  EXPECT_EQ(dif_alert_handler_alert_is_cause(&alert_handler_, kAlerts, &flag),
            kDifBadArg);
  EXPECT_EQ(dif_alert_handler_alert_acknowledge(&alert_handler_, kAlerts),
            kDifBadArg);
}

TEST_F(CauseTest, IsCauseLocal) {
  bool flag;

  EXPECT_READ32(ALERT_HANDLER_LOC_ALERT_CAUSE_1_REG_OFFSET,
                {{ALERT_HANDLER_LOC_ALERT_CAUSE_1_LA_1_BIT, true}});
  EXPECT_EQ(
      dif_alert_handler_local_alert_is_cause(
          &alert_handler_, kDifAlertHandlerLocalAlertEscalationPingFail, &flag),
      kDifOk);
  EXPECT_TRUE(flag);

  EXPECT_READ32(ALERT_HANDLER_LOC_ALERT_CAUSE_4_REG_OFFSET,
                {{ALERT_HANDLER_LOC_ALERT_CAUSE_4_LA_4_BIT, true}});
  EXPECT_EQ(
      dif_alert_handler_local_alert_is_cause(
          &alert_handler_, kDifAlertHandlerLocalAlertBusIntegrityFail, &flag),
      kDifOk);
  EXPECT_TRUE(flag);

  EXPECT_READ32(ALERT_HANDLER_LOC_ALERT_CAUSE_3_REG_OFFSET,
                {{ALERT_HANDLER_LOC_ALERT_CAUSE_3_LA_3_BIT, false}});
  EXPECT_EQ(dif_alert_handler_local_alert_is_cause(
                &alert_handler_,
                kDifAlertHandlerLocalAlertEscalationIntegrityFail, &flag),
            kDifOk);
  EXPECT_FALSE(flag);
}

TEST_F(CauseTest, AckLocal) {
  EXPECT_WRITE32(ALERT_HANDLER_LOC_ALERT_CAUSE_3_REG_OFFSET,
                 {{ALERT_HANDLER_LOC_ALERT_CAUSE_3_LA_3_BIT, true}});
  EXPECT_EQ(
      dif_alert_handler_local_alert_acknowledge(
          &alert_handler_, kDifAlertHandlerLocalAlertEscalationIntegrityFail),
      kDifOk);

  EXPECT_WRITE32(ALERT_HANDLER_LOC_ALERT_CAUSE_4_REG_OFFSET,
                 {{ALERT_HANDLER_LOC_ALERT_CAUSE_4_LA_4_BIT, true}});
  EXPECT_EQ(dif_alert_handler_local_alert_acknowledge(
                &alert_handler_, kDifAlertHandlerLocalAlertBusIntegrityFail),
            kDifOk);
}

TEST_F(CauseTest, NullArgs) {
  bool flag;
  EXPECT_EQ(dif_alert_handler_alert_is_cause(nullptr, 5, &flag), kDifBadArg);
  EXPECT_EQ(dif_alert_handler_alert_is_cause(&alert_handler_, 5, nullptr),
            kDifBadArg);
  EXPECT_EQ(dif_alert_handler_alert_acknowledge(nullptr, 11), kDifBadArg);
  EXPECT_EQ(dif_alert_handler_local_alert_is_cause(
                nullptr, kDifAlertHandlerLocalAlertEscalationPingFail, &flag),
            kDifBadArg);
  EXPECT_EQ(dif_alert_handler_local_alert_is_cause(
                &alert_handler_, kDifAlertHandlerLocalAlertEscalationPingFail,
                nullptr),
            kDifBadArg);
  EXPECT_EQ(dif_alert_handler_local_alert_acknowledge(
                nullptr, kDifAlertHandlerLocalAlertEscalationIntegrityFail),
            kDifBadArg);
}

class EscalationTest : public AlertHandlerTest {};

TEST_F(EscalationTest, CanClear) {
  bool flag;

  EXPECT_READ32(ALERT_HANDLER_CLASSB_CLR_REGWEN_REG_OFFSET, true);
  EXPECT_EQ(dif_alert_handler_escalation_can_clear(
                &alert_handler_, kDifAlertHandlerClassB, &flag),
            kDifOk);
  EXPECT_TRUE(flag);

  EXPECT_READ32(ALERT_HANDLER_CLASSA_CLR_REGWEN_REG_OFFSET, false);
  EXPECT_EQ(dif_alert_handler_escalation_can_clear(
                &alert_handler_, kDifAlertHandlerClassA, &flag),
            kDifOk);
  EXPECT_FALSE(flag);
}

TEST_F(EscalationTest, Disable) {
  EXPECT_WRITE32(ALERT_HANDLER_CLASSC_CLR_REGWEN_REG_OFFSET, true);
  EXPECT_EQ(dif_alert_handler_escalation_disable_clearing(
                &alert_handler_, kDifAlertHandlerClassC),
            kDifOk);
}

TEST_F(EscalationTest, Clear) {
  EXPECT_WRITE32_SHADOWED(ALERT_HANDLER_CLASSD_CLR_SHADOWED_REG_OFFSET, true);
  EXPECT_EQ(dif_alert_handler_escalation_clear(&alert_handler_,
                                               kDifAlertHandlerClassD),
            kDifOk);
}

TEST_F(EscalationTest, NullArgs) {
  bool flag;

  EXPECT_EQ(dif_alert_handler_escalation_can_clear(
                nullptr, kDifAlertHandlerClassB, &flag),
            kDifBadArg);
  EXPECT_EQ(dif_alert_handler_escalation_can_clear(
                &alert_handler_, kDifAlertHandlerClassB, nullptr),
            kDifBadArg);
  EXPECT_EQ(dif_alert_handler_escalation_disable_clearing(
                nullptr, kDifAlertHandlerClassC),
            kDifBadArg);
  EXPECT_EQ(dif_alert_handler_escalation_clear(nullptr, kDifAlertHandlerClassD),
            kDifBadArg);
}

class GetterTest : public AlertHandlerTest {};

TEST_F(GetterTest, GetAcc) {
  uint16_t alerts;
  EXPECT_READ32(ALERT_HANDLER_CLASSB_ACCUM_CNT_REG_OFFSET, 0xaaaa);
  EXPECT_EQ(dif_alert_handler_get_accumulator(&alert_handler_,
                                              kDifAlertHandlerClassB, &alerts),
            kDifOk);
  EXPECT_EQ(alerts, 0xaaaa);
}

TEST_F(GetterTest, GetCycles) {
  uint32_t cycles;
  EXPECT_READ32(ALERT_HANDLER_CLASSD_ESC_CNT_REG_OFFSET, 0xaaaaaaaa);
  EXPECT_EQ(dif_alert_handler_get_escalation_counter(
                &alert_handler_, kDifAlertHandlerClassD, &cycles),
            kDifOk);
  EXPECT_EQ(cycles, 0xaaaaaaaa);
}

TEST_F(GetterTest, GetState) {
  dif_alert_handler_class_state_t state;

  EXPECT_READ32(ALERT_HANDLER_CLASSC_STATE_REG_OFFSET,
                ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_VALUE_TIMEOUT);
  EXPECT_EQ(dif_alert_handler_get_class_state(&alert_handler_,
                                              kDifAlertHandlerClassC, &state),
            kDifOk);
  EXPECT_EQ(state, kDifAlertHandlerClassStateTimeout);

  EXPECT_READ32(ALERT_HANDLER_CLASSA_STATE_REG_OFFSET,
                ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_VALUE_PHASE2);
  EXPECT_EQ(dif_alert_handler_get_class_state(&alert_handler_,
                                              kDifAlertHandlerClassA, &state),
            kDifOk);
  EXPECT_EQ(state, kDifAlertHandlerClassStatePhase2);
}

TEST_F(GetterTest, NullArgs) {
  uint16_t alerts;
  EXPECT_EQ(dif_alert_handler_get_accumulator(nullptr, kDifAlertHandlerClassB,
                                              &alerts),
            kDifBadArg);
  EXPECT_EQ(dif_alert_handler_get_accumulator(&alert_handler_,
                                              kDifAlertHandlerClassB, nullptr),
            kDifBadArg);

  uint32_t cycles;
  EXPECT_EQ(dif_alert_handler_get_escalation_counter(
                nullptr, kDifAlertHandlerClassB, &cycles),
            kDifBadArg);
  EXPECT_EQ(dif_alert_handler_get_escalation_counter(
                &alert_handler_, kDifAlertHandlerClassB, nullptr),
            kDifBadArg);

  dif_alert_handler_class_state_t state;
  EXPECT_EQ(dif_alert_handler_get_class_state(nullptr, kDifAlertHandlerClassC,
                                              &state),
            kDifBadArg);
  EXPECT_EQ(dif_alert_handler_get_class_state(&alert_handler_,
                                              kDifAlertHandlerClassC, nullptr),
            kDifBadArg);
}

}  // namespace
}  // namespace dif_alert_handler_unittest
