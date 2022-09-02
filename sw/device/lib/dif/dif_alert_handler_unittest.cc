// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_alert_handler.h"

#include <cstring>
#include <limits>
#include <ostream>
#include <tuple>
#include <vector>

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "alert_handler_regs.h"  // Generated.

namespace dif_alert_handler_unittest {
namespace {
using ::mock_mmio::LeInt;
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::_;
using ::testing::Return;

// If the assert below fails, please look at #14038.
// A digest is calculated for the configuration of the alerts,
// so if the number of alerts change, the digest will be changed
// as well.  This process is not yet automated, so the user
// must be aware on how to update the value.
static_assert(ALERT_HANDLER_PARAM_N_ALERTS == 65,
              "The number of alerts have changed.");

constexpr int kAlerts = ALERT_HANDLER_PARAM_N_ALERTS;
constexpr int kLocalAlerts = ALERT_HANDLER_PARAM_N_LOC_ALERT;
constexpr int kClasses = ALERT_HANDLER_PARAM_N_CLASSES;
constexpr int kEscSignals = ALERT_HANDLER_PARAM_N_ESC_SEV;

class AlertHandlerTest : public testing::Test, public MmioTest {
 protected:
  dif_alert_handler_t alert_handler_ = {.base_addr = dev().region()};
};

class AlertConfigTest : public AlertHandlerTest,
                        public testing::WithParamInterface<
                            std::tuple<int, dif_alert_handler_class_t>> {};

TEST_F(AlertConfigTest, BadArgs) {
  EXPECT_DIF_BADARG(
      dif_alert_handler_configure_alert(nullptr, 0, kDifAlertHandlerClassA,
                                        kDifToggleEnabled, kDifToggleDisabled));

  EXPECT_DIF_BADARG(dif_alert_handler_configure_alert(
      &alert_handler_, kAlerts, kDifAlertHandlerClassA, kDifToggleEnabled,
      kDifToggleDisabled));

  EXPECT_DIF_BADARG(dif_alert_handler_configure_alert(
      &alert_handler_, 0, static_cast<dif_alert_handler_class_t>(kClasses),
      kDifToggleEnabled, kDifToggleDisabled));

  EXPECT_DIF_BADARG(dif_alert_handler_configure_alert(
      &alert_handler_, 0, kDifAlertHandlerClassA, static_cast<dif_toggle_t>(2),
      kDifToggleDisabled));

  EXPECT_DIF_BADARG(dif_alert_handler_configure_alert(
      &alert_handler_, 0, kDifAlertHandlerClassA, kDifToggleEnabled,
      static_cast<dif_toggle_t>(2)));
}

TEST_F(AlertConfigTest, Locked) {
  EXPECT_READ32(ALERT_HANDLER_ALERT_REGWEN_0_REG_OFFSET, 0);
  EXPECT_EQ(dif_alert_handler_configure_alert(
                &alert_handler_, 0, kDifAlertHandlerClassA, kDifToggleEnabled,
                kDifToggleDisabled),
            kDifLocked);

  EXPECT_READ32(ALERT_HANDLER_ALERT_REGWEN_0_REG_OFFSET +
                    (kAlerts - 1) * sizeof(uint32_t),
                0);
  EXPECT_EQ(dif_alert_handler_configure_alert(
                &alert_handler_, kAlerts - 1, kDifAlertHandlerClassD,
                kDifToggleEnabled, kDifToggleEnabled),
            kDifLocked);
}

TEST_P(AlertConfigTest, EnableOnly) {
  dif_alert_handler_alert_t alert = std::get<0>(GetParam());
  dif_alert_handler_class_t alert_class = std::get<1>(GetParam());

  EXPECT_READ32(
      ALERT_HANDLER_ALERT_REGWEN_0_REG_OFFSET + alert * sizeof(uint32_t),
      ALERT_HANDLER_ALERT_REGWEN_0_REG_RESVAL);
  EXPECT_WRITE32_SHADOWED(
      ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_REG_OFFSET +
          alert * sizeof(uint32_t),
      {{ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_CLASS_A_0_OFFSET, alert_class}});
  EXPECT_WRITE32_SHADOWED(
      ALERT_HANDLER_ALERT_EN_SHADOWED_0_REG_OFFSET + alert * sizeof(uint32_t),
      {{ALERT_HANDLER_ALERT_EN_SHADOWED_0_EN_A_0_BIT, true}});

  EXPECT_DIF_OK(
      dif_alert_handler_configure_alert(&alert_handler_, alert, alert_class,
                                        kDifToggleEnabled, kDifToggleDisabled));
}

TEST_P(AlertConfigTest, EnableAndLock) {
  dif_alert_handler_alert_t alert = std::get<0>(GetParam());
  dif_alert_handler_class_t alert_class = std::get<1>(GetParam());

  EXPECT_READ32(
      ALERT_HANDLER_ALERT_REGWEN_0_REG_OFFSET + alert * sizeof(uint32_t),
      ALERT_HANDLER_ALERT_REGWEN_0_REG_RESVAL);
  EXPECT_WRITE32_SHADOWED(
      ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_REG_OFFSET +
          alert * sizeof(uint32_t),
      {{ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_CLASS_A_0_OFFSET, alert_class}});
  EXPECT_WRITE32_SHADOWED(
      ALERT_HANDLER_ALERT_EN_SHADOWED_0_REG_OFFSET + alert * sizeof(uint32_t),
      {{ALERT_HANDLER_ALERT_EN_SHADOWED_0_EN_A_0_BIT, true}});
  EXPECT_WRITE32(
      ALERT_HANDLER_ALERT_REGWEN_0_REG_OFFSET + alert * sizeof(uint32_t), 0);

  EXPECT_DIF_OK(
      dif_alert_handler_configure_alert(&alert_handler_, alert, alert_class,
                                        kDifToggleEnabled, kDifToggleEnabled));
}

INSTANTIATE_TEST_SUITE_P(
    AllAlertsAndClasses, AlertConfigTest,
    testing::Combine(testing::Range(0, kAlerts),
                     testing::Values(kDifAlertHandlerClassA,
                                     kDifAlertHandlerClassB,
                                     kDifAlertHandlerClassC,
                                     kDifAlertHandlerClassD)));

class LocalAlertConfigTest
    : public AlertHandlerTest,
      public testing::WithParamInterface<std::tuple<
          dif_alert_handler_local_alert_t, dif_alert_handler_class_t>> {};

TEST_F(LocalAlertConfigTest, BadArgs) {
  EXPECT_DIF_BADARG(dif_alert_handler_configure_local_alert(
      nullptr, kDifAlertHandlerLocalAlertBusIntegrityFail,
      kDifAlertHandlerClassA, kDifToggleEnabled, kDifToggleDisabled));

  EXPECT_DIF_BADARG(dif_alert_handler_configure_local_alert(
      &alert_handler_,
      static_cast<dif_alert_handler_local_alert_t>(kLocalAlerts),
      kDifAlertHandlerClassA, kDifToggleEnabled, kDifToggleDisabled));

  EXPECT_DIF_BADARG(dif_alert_handler_configure_local_alert(
      &alert_handler_, kDifAlertHandlerLocalAlertAlertPingFail,
      static_cast<dif_alert_handler_class_t>(kClasses), kDifToggleEnabled,
      kDifToggleDisabled));

  EXPECT_DIF_BADARG(dif_alert_handler_configure_local_alert(
      &alert_handler_, kDifAlertHandlerLocalAlertAlertPingFail,
      kDifAlertHandlerClassA, static_cast<dif_toggle_t>(2),
      kDifToggleDisabled));

  EXPECT_DIF_BADARG(dif_alert_handler_configure_local_alert(
      &alert_handler_, kDifAlertHandlerLocalAlertAlertPingFail,
      kDifAlertHandlerClassA, kDifToggleEnabled, static_cast<dif_toggle_t>(2)));
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
      ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_REG_OFFSET +
          static_cast<uint32_t>(local_alert) * sizeof(uint32_t),
      {{ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_CLASS_LA_0_OFFSET,
        alert_class}});
  EXPECT_WRITE32_SHADOWED(
      ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_0_REG_OFFSET +
          static_cast<uint32_t>(local_alert) * sizeof(uint32_t),
      {{ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_0_EN_LA_0_BIT, true}});

  EXPECT_DIF_OK(dif_alert_handler_configure_local_alert(
      &alert_handler_, local_alert, alert_class, kDifToggleEnabled,
      kDifToggleDisabled));
}

TEST_P(LocalAlertConfigTest, EnableAndLock) {
  dif_alert_handler_local_alert_t local_alert = std::get<0>(GetParam());
  dif_alert_handler_class_t alert_class = std::get<1>(GetParam());

  EXPECT_READ32(ALERT_HANDLER_LOC_ALERT_REGWEN_0_REG_OFFSET +
                    static_cast<uint32_t>(local_alert) * sizeof(uint32_t),
                ALERT_HANDLER_LOC_ALERT_REGWEN_0_REG_RESVAL);
  EXPECT_WRITE32_SHADOWED(
      ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_REG_OFFSET +
          static_cast<uint32_t>(local_alert) * sizeof(uint32_t),
      {{ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_CLASS_LA_0_OFFSET,
        alert_class}});
  EXPECT_WRITE32_SHADOWED(
      ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_0_REG_OFFSET +
          static_cast<uint32_t>(local_alert) * sizeof(uint32_t),
      {{ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_0_EN_LA_0_BIT, true}});
  EXPECT_WRITE32(ALERT_HANDLER_LOC_ALERT_REGWEN_0_REG_OFFSET +
                     static_cast<uint32_t>(local_alert) * sizeof(uint32_t),
                 0);

  EXPECT_DIF_OK(dif_alert_handler_configure_local_alert(
      &alert_handler_, local_alert, alert_class, kDifToggleEnabled,
      kDifToggleEnabled));
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

class ClassConfigTest : public AlertHandlerTest {};

TEST_F(ClassConfigTest, BadArgs) {
  dif_alert_handler_class_config_t valid_config = {
      .auto_lock_accumulation_counter = kDifToggleDisabled,
      .accumulator_threshold = 10,
      .irq_deadline_cycles = 10000,
      .escalation_phases = nullptr,
      .escalation_phases_len = 0,
      .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase1,
  };

  EXPECT_DIF_BADARG(dif_alert_handler_configure_class(
      nullptr, kDifAlertHandlerClassB, valid_config, kDifToggleEnabled,
      kDifToggleDisabled));

  EXPECT_DIF_BADARG(dif_alert_handler_configure_class(
      &alert_handler_, static_cast<dif_alert_handler_class_t>(kClasses),
      valid_config, kDifToggleEnabled, kDifToggleDisabled));

  EXPECT_DIF_BADARG(dif_alert_handler_configure_class(
      &alert_handler_, static_cast<dif_alert_handler_class_t>(kClasses),
      valid_config, static_cast<dif_toggle_t>(2), kDifToggleDisabled));

  EXPECT_DIF_BADARG(dif_alert_handler_configure_class(
      &alert_handler_, static_cast<dif_alert_handler_class_t>(kClasses),
      valid_config, kDifToggleEnabled, static_cast<dif_toggle_t>(2)));
}

TEST_F(ClassConfigTest, BadConfig) {
  dif_alert_handler_class_config_t config = {
      .auto_lock_accumulation_counter = kDifToggleDisabled,
      .accumulator_threshold = 10,
      .irq_deadline_cycles = 10000,
      .escalation_phases = nullptr,
      .escalation_phases_len = 0,
      .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase1};
  dif_alert_handler_escalation_phase_t esc_phase = {
      .phase = kDifAlertHandlerClassStatePhase2,
      .signal = 0,
      .duration_cycles = 10000};

  // Bad auto_lock_accumulation_counter flag.
  config.auto_lock_accumulation_counter = static_cast<dif_toggle_t>(2);
  EXPECT_DIF_BADARG(
      dif_alert_handler_configure_class(nullptr, kDifAlertHandlerClassB, config,
                                        kDifToggleEnabled, kDifToggleDisabled));
  config.auto_lock_accumulation_counter = kDifToggleDisabled;

  // Bad escalation_phases array dimension.
  config.escalation_phases_len = 1;
  EXPECT_DIF_BADARG(
      dif_alert_handler_configure_class(nullptr, kDifAlertHandlerClassB, config,
                                        kDifToggleEnabled, kDifToggleDisabled));
  config.escalation_phases_len = 0;
  config.escalation_phases = &esc_phase;
  EXPECT_DIF_BADARG(
      dif_alert_handler_configure_class(nullptr, kDifAlertHandlerClassB, config,
                                        kDifToggleEnabled, kDifToggleDisabled));
  config.escalation_phases = nullptr;

  // Bad crashdump_escalation_phase.
  config.crashdump_escalation_phase = kDifAlertHandlerClassStateTimeout;
  EXPECT_DIF_BADARG(
      dif_alert_handler_configure_class(nullptr, kDifAlertHandlerClassB, config,
                                        kDifToggleEnabled, kDifToggleDisabled));
  config.crashdump_escalation_phase = kDifAlertHandlerClassStateTerminal;
  EXPECT_DIF_BADARG(
      dif_alert_handler_configure_class(nullptr, kDifAlertHandlerClassB, config,
                                        kDifToggleEnabled, kDifToggleDisabled));
  config.crashdump_escalation_phase = kDifAlertHandlerClassStatePhase1;
}

TEST_F(ClassConfigTest, BadEscPhaseConfig) {
  std::vector<dif_alert_handler_escalation_phase_t> esc_phases = {
      {.phase = kDifAlertHandlerClassStatePhase0,
       .signal = 3,
       .duration_cycles = 5000},
      {.phase = kDifAlertHandlerClassStatePhase2,
       .signal = 1,
       .duration_cycles = 1000},
  };
  dif_alert_handler_class_config_t config = {
      .auto_lock_accumulation_counter = kDifToggleDisabled,
      .accumulator_threshold = 10,
      .irq_deadline_cycles = 10000,
      .escalation_phases = esc_phases.data(),
      .escalation_phases_len = 1,
      .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase1,
  };

  // Bad phase.
  esc_phases[0].phase = kDifAlertHandlerClassStateTerminal;
  EXPECT_DIF_BADARG(
      dif_alert_handler_configure_class(nullptr, kDifAlertHandlerClassB, config,
                                        kDifToggleEnabled, kDifToggleDisabled));
  esc_phases[0].phase = kDifAlertHandlerClassStatePhase2;

  // Bad signal.
  esc_phases[0].signal = kEscSignals;
  EXPECT_DIF_BADARG(
      dif_alert_handler_configure_class(nullptr, kDifAlertHandlerClassB, config,
                                        kDifToggleEnabled, kDifToggleDisabled));
  esc_phases[0].signal = 0;
}

TEST_F(ClassConfigTest, Locked) {
  dif_alert_handler_class_config_t config = {
      .auto_lock_accumulation_counter = kDifToggleDisabled,
      .accumulator_threshold = 10,
      .irq_deadline_cycles = 10000,
      .escalation_phases = nullptr,
      .escalation_phases_len = 0,
      .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase1,
  };

  EXPECT_READ32(ALERT_HANDLER_CLASSC_REGWEN_REG_OFFSET, 0);
  EXPECT_EQ(dif_alert_handler_configure_class(
                &alert_handler_, kDifAlertHandlerClassC, config,
                kDifToggleEnabled, kDifToggleDisabled),
            kDifLocked);
}

TEST_F(ClassConfigTest, EnableOnly) {
  std::vector<dif_alert_handler_escalation_phase_t> esc_phases = {
      {.phase = kDifAlertHandlerClassStatePhase0,
       .signal = 3,
       .duration_cycles = 5000},
      {.phase = kDifAlertHandlerClassStatePhase2,
       .signal = 1,
       .duration_cycles = 1000},
  };
  dif_alert_handler_class_config_t config = {
      .auto_lock_accumulation_counter = kDifToggleDisabled,
      .accumulator_threshold = 10,
      .irq_deadline_cycles = 10000,
      .escalation_phases = esc_phases.data(),
      .escalation_phases_len = esc_phases.size(),
      .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase1,
  };

  EXPECT_READ32(ALERT_HANDLER_CLASSC_REGWEN_REG_OFFSET, 1);

  EXPECT_WRITE32_SHADOWED(ALERT_HANDLER_CLASSC_PHASE0_CYC_SHADOWED_REG_OFFSET,
                          esc_phases[0].duration_cycles);
  EXPECT_WRITE32_SHADOWED(ALERT_HANDLER_CLASSC_PHASE2_CYC_SHADOWED_REG_OFFSET,
                          esc_phases[1].duration_cycles);

  EXPECT_WRITE32_SHADOWED(ALERT_HANDLER_CLASSC_ACCUM_THRESH_SHADOWED_REG_OFFSET,
                          config.accumulator_threshold);

  EXPECT_WRITE32_SHADOWED(ALERT_HANDLER_CLASSC_TIMEOUT_CYC_SHADOWED_REG_OFFSET,
                          config.irq_deadline_cycles);

  EXPECT_WRITE32_SHADOWED(
      ALERT_HANDLER_CLASSC_CRASHDUMP_TRIGGER_SHADOWED_REG_OFFSET, 1);

  uint32_t ctrl_reg = 0;
  ctrl_reg = bitfield_bit32_write(ctrl_reg,
                                  ALERT_HANDLER_CLASSC_CTRL_SHADOWED_EN_BIT, 1);
  ctrl_reg = bitfield_bit32_write(
      ctrl_reg, ALERT_HANDLER_CLASSC_CTRL_SHADOWED_EN_E3_BIT, 1);
  ctrl_reg = bitfield_bit32_write(
      ctrl_reg, ALERT_HANDLER_CLASSC_CTRL_SHADOWED_EN_E1_BIT, 1);
  ctrl_reg = bitfield_field32_write(
      ctrl_reg, ALERT_HANDLER_CLASSC_CTRL_SHADOWED_MAP_E3_FIELD, 0);
  ctrl_reg = bitfield_field32_write(
      ctrl_reg, ALERT_HANDLER_CLASSC_CTRL_SHADOWED_MAP_E1_FIELD, 2);
  EXPECT_WRITE32_SHADOWED(ALERT_HANDLER_CLASSC_CTRL_SHADOWED_REG_OFFSET,
                          ctrl_reg);

  EXPECT_DIF_OK(dif_alert_handler_configure_class(
      &alert_handler_, kDifAlertHandlerClassC, config, kDifToggleEnabled,
      kDifToggleDisabled));
}

TEST_F(ClassConfigTest, EnableAndLock) {
  std::vector<dif_alert_handler_escalation_phase_t> esc_phases = {
      {.phase = kDifAlertHandlerClassStatePhase0,
       .signal = 1,
       .duration_cycles = 5000},
      {.phase = kDifAlertHandlerClassStatePhase2,
       .signal = 3,
       .duration_cycles = 1000},
  };
  dif_alert_handler_class_config_t config = {
      .auto_lock_accumulation_counter = kDifToggleEnabled,
      .accumulator_threshold = 10,
      .irq_deadline_cycles = 10000,
      .escalation_phases = esc_phases.data(),
      .escalation_phases_len = esc_phases.size(),
      .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase1,
  };

  EXPECT_READ32(ALERT_HANDLER_CLASSC_REGWEN_REG_OFFSET, 1);

  EXPECT_WRITE32_SHADOWED(ALERT_HANDLER_CLASSC_PHASE0_CYC_SHADOWED_REG_OFFSET,
                          esc_phases[0].duration_cycles);
  EXPECT_WRITE32_SHADOWED(ALERT_HANDLER_CLASSC_PHASE2_CYC_SHADOWED_REG_OFFSET,
                          esc_phases[1].duration_cycles);

  EXPECT_WRITE32_SHADOWED(ALERT_HANDLER_CLASSC_ACCUM_THRESH_SHADOWED_REG_OFFSET,
                          config.accumulator_threshold);

  EXPECT_WRITE32_SHADOWED(ALERT_HANDLER_CLASSC_TIMEOUT_CYC_SHADOWED_REG_OFFSET,
                          config.irq_deadline_cycles);

  EXPECT_WRITE32_SHADOWED(
      ALERT_HANDLER_CLASSC_CRASHDUMP_TRIGGER_SHADOWED_REG_OFFSET, 1);

  uint32_t ctrl_reg = 0;
  ctrl_reg = bitfield_bit32_write(ctrl_reg,
                                  ALERT_HANDLER_CLASSC_CTRL_SHADOWED_EN_BIT, 1);
  ctrl_reg = bitfield_bit32_write(
      ctrl_reg, ALERT_HANDLER_CLASSC_CTRL_SHADOWED_LOCK_BIT, 1);
  ctrl_reg = bitfield_bit32_write(
      ctrl_reg, ALERT_HANDLER_CLASSC_CTRL_SHADOWED_EN_E1_BIT, 1);
  ctrl_reg = bitfield_bit32_write(
      ctrl_reg, ALERT_HANDLER_CLASSC_CTRL_SHADOWED_EN_E3_BIT, 1);
  ctrl_reg = bitfield_field32_write(
      ctrl_reg, ALERT_HANDLER_CLASSC_CTRL_SHADOWED_MAP_E1_FIELD, 0);
  ctrl_reg = bitfield_field32_write(
      ctrl_reg, ALERT_HANDLER_CLASSC_CTRL_SHADOWED_MAP_E3_FIELD, 2);
  EXPECT_WRITE32_SHADOWED(ALERT_HANDLER_CLASSC_CTRL_SHADOWED_REG_OFFSET,
                          ctrl_reg);

  EXPECT_WRITE32(ALERT_HANDLER_CLASSC_REGWEN_REG_OFFSET, 0);

  EXPECT_DIF_OK(dif_alert_handler_configure_class(
      &alert_handler_, kDifAlertHandlerClassC, config, kDifToggleEnabled,
      kDifToggleEnabled));
}

class PingTimerConfigTest : public AlertHandlerTest {};

TEST_F(PingTimerConfigTest, BadArgs) {
  EXPECT_DIF_BADARG(dif_alert_handler_configure_ping_timer(
      nullptr, 0, kDifToggleDisabled, kDifToggleDisabled));

  EXPECT_DIF_BADARG(dif_alert_handler_configure_ping_timer(
      &alert_handler_, 0, static_cast<dif_toggle_t>(2), kDifToggleDisabled));

  EXPECT_DIF_BADARG(dif_alert_handler_configure_ping_timer(
      &alert_handler_, 0, kDifToggleDisabled, static_cast<dif_toggle_t>(2)));
}

TEST_F(PingTimerConfigTest, TimeoutTooBig) {
  uint32_t ping_timeout =
      ALERT_HANDLER_PING_TIMEOUT_CYC_SHADOWED_PING_TIMEOUT_CYC_SHADOWED_MASK +
      1;

  EXPECT_DIF_BADARG(dif_alert_handler_configure_ping_timer(
      &alert_handler_, ping_timeout, kDifToggleDisabled, kDifToggleDisabled));
}

TEST_F(PingTimerConfigTest, Locked) {
  EXPECT_READ32(ALERT_HANDLER_PING_TIMER_REGWEN_REG_OFFSET, 0);

  EXPECT_EQ(dif_alert_handler_configure_ping_timer(
                &alert_handler_, 5000, kDifToggleDisabled, kDifToggleDisabled),
            kDifLocked);
}

TEST_F(PingTimerConfigTest, ConfigureAndEnable) {
  uint32_t ping_timeout = 5000;

  EXPECT_READ32(ALERT_HANDLER_PING_TIMER_REGWEN_REG_OFFSET, 1);
  EXPECT_WRITE32_SHADOWED(ALERT_HANDLER_PING_TIMEOUT_CYC_SHADOWED_REG_OFFSET,
                          ping_timeout);
  EXPECT_WRITE32_SHADOWED(ALERT_HANDLER_PING_TIMER_EN_SHADOWED_REG_OFFSET, 1);

  EXPECT_DIF_OK(dif_alert_handler_configure_ping_timer(
      &alert_handler_, ping_timeout, kDifToggleEnabled, kDifToggleDisabled));
}

TEST_F(PingTimerConfigTest, ConfigureEnableAndLock) {
  uint32_t ping_timeout = 5000;

  EXPECT_READ32(ALERT_HANDLER_PING_TIMER_REGWEN_REG_OFFSET, 1);
  EXPECT_WRITE32_SHADOWED(ALERT_HANDLER_PING_TIMEOUT_CYC_SHADOWED_REG_OFFSET,
                          ping_timeout);
  EXPECT_WRITE32_SHADOWED(ALERT_HANDLER_PING_TIMER_EN_SHADOWED_REG_OFFSET, 1);
  EXPECT_WRITE32(ALERT_HANDLER_PING_TIMER_REGWEN_REG_OFFSET, 0);

  EXPECT_DIF_OK(dif_alert_handler_configure_ping_timer(
      &alert_handler_, ping_timeout, kDifToggleEnabled, kDifToggleEnabled));
}

class PingTimerSetEnabledTest : public AlertHandlerTest {};

TEST_F(PingTimerSetEnabledTest, BadArgs) {
  EXPECT_DIF_BADARG(
      dif_alert_handler_ping_timer_set_enabled(nullptr, kDifToggleDisabled));

  EXPECT_DIF_BADARG(dif_alert_handler_ping_timer_set_enabled(
      &alert_handler_, static_cast<dif_toggle_t>(2)));
}

TEST_F(PingTimerSetEnabledTest, Locked) {
  EXPECT_READ32(ALERT_HANDLER_PING_TIMER_REGWEN_REG_OFFSET, 0);

  EXPECT_EQ(dif_alert_handler_ping_timer_set_enabled(&alert_handler_,
                                                     kDifToggleDisabled),
            kDifLocked);
}

TEST_F(PingTimerSetEnabledTest, SetEnabled) {
  EXPECT_READ32(ALERT_HANDLER_PING_TIMER_REGWEN_REG_OFFSET, 1);
  EXPECT_WRITE32_SHADOWED(ALERT_HANDLER_PING_TIMER_EN_SHADOWED_REG_OFFSET, 1);

  EXPECT_DIF_OK(dif_alert_handler_ping_timer_set_enabled(&alert_handler_,
                                                         kDifToggleDisabled));
}

TEST_F(PingTimerSetEnabledTest, SetEnabledAndLock) {
  EXPECT_READ32(ALERT_HANDLER_PING_TIMER_REGWEN_REG_OFFSET, 1);
  EXPECT_WRITE32_SHADOWED(ALERT_HANDLER_PING_TIMER_EN_SHADOWED_REG_OFFSET, 1);
  EXPECT_WRITE32(ALERT_HANDLER_PING_TIMER_REGWEN_REG_OFFSET, 0);

  EXPECT_DIF_OK(dif_alert_handler_ping_timer_set_enabled(&alert_handler_,
                                                         kDifToggleEnabled));
}

class AlertLockTest : public AlertHandlerTest,
                      public testing::WithParamInterface<int> {};

TEST_P(AlertLockTest, IsAlertLocked) {
  dif_alert_handler_alert_t alert = GetParam();
  bool is_locked = true;

  ptrdiff_t regwen_offset =
      ALERT_HANDLER_ALERT_REGWEN_0_REG_OFFSET + alert * sizeof(uint32_t);
  EXPECT_READ32(regwen_offset, ALERT_HANDLER_ALERT_REGWEN_0_REG_RESVAL);
  EXPECT_DIF_OK(
      dif_alert_handler_is_alert_locked(&alert_handler_, alert, &is_locked));
  EXPECT_FALSE(is_locked);

  is_locked = false;
  EXPECT_READ32(regwen_offset, 0);
  EXPECT_DIF_OK(
      dif_alert_handler_is_alert_locked(&alert_handler_, alert, &is_locked));
  EXPECT_TRUE(is_locked);
}

INSTANTIATE_TEST_SUITE_P(AllAlertsLockedAndUnlocked, AlertLockTest,
                         testing::Range(0, kAlerts));

TEST_P(AlertLockTest, LockAlert) {
  dif_alert_handler_alert_t alert = GetParam();

  ptrdiff_t regwen_offset =
      ALERT_HANDLER_ALERT_REGWEN_0_REG_OFFSET + alert * sizeof(uint32_t);
  EXPECT_WRITE32(regwen_offset, 0);
  EXPECT_DIF_OK(dif_alert_handler_lock_alert(&alert_handler_, alert));
}

INSTANTIATE_TEST_SUITE_P(LockAllAlerts, AlertLockTest,
                         testing::Range(0, kAlerts));

TEST_F(AlertLockTest, BadArgs) {
  bool is_locked;
  EXPECT_DIF_BADARG(dif_alert_handler_is_alert_locked(nullptr, 0, &is_locked));
  EXPECT_DIF_BADARG(
      dif_alert_handler_is_alert_locked(&alert_handler_, kAlerts, &is_locked));
  EXPECT_DIF_BADARG(
      dif_alert_handler_is_alert_locked(&alert_handler_, 0, nullptr));

  EXPECT_DIF_BADARG(dif_alert_handler_lock_alert(nullptr, 0));
  EXPECT_DIF_BADARG(dif_alert_handler_lock_alert(&alert_handler_, kAlerts));
}

class LocalAlertLockTest
    : public AlertHandlerTest,
      public testing::WithParamInterface<dif_alert_handler_local_alert_t> {};

TEST_P(LocalAlertLockTest, IsLocalAlertLocked) {
  dif_alert_handler_local_alert_t local_alert = GetParam();
  bool is_locked = true;

  EXPECT_READ32(ALERT_HANDLER_LOC_ALERT_REGWEN_0_REG_OFFSET +
                    static_cast<uint32_t>(local_alert) * sizeof(uint32_t),
                ALERT_HANDLER_LOC_ALERT_REGWEN_0_REG_RESVAL);
  EXPECT_DIF_OK(dif_alert_handler_is_local_alert_locked(
      &alert_handler_, local_alert, &is_locked));
  EXPECT_FALSE(is_locked);

  is_locked = false;
  EXPECT_READ32(ALERT_HANDLER_LOC_ALERT_REGWEN_0_REG_OFFSET +
                    static_cast<uint32_t>(local_alert) * sizeof(uint32_t),
                0);
  EXPECT_DIF_OK(dif_alert_handler_is_local_alert_locked(
      &alert_handler_, local_alert, &is_locked));
  EXPECT_TRUE(is_locked);
}

INSTANTIATE_TEST_SUITE_P(
    AllLocalAlertsLockedAndUnlocked, LocalAlertLockTest,
    testing::Values(kDifAlertHandlerLocalAlertAlertPingFail,
                    kDifAlertHandlerLocalAlertEscalationPingFail,
                    kDifAlertHandlerLocalAlertAlertIntegrityFail,
                    kDifAlertHandlerLocalAlertEscalationIntegrityFail,
                    kDifAlertHandlerLocalAlertBusIntegrityFail,
                    kDifAlertHandlerLocalAlertShadowedUpdateError,
                    kDifAlertHandlerLocalAlertShadowedStorageError));

TEST_P(LocalAlertLockTest, LockLocalAlert) {
  dif_alert_handler_local_alert_t local_alert = GetParam();

  EXPECT_WRITE32(ALERT_HANDLER_LOC_ALERT_REGWEN_0_REG_OFFSET +
                     static_cast<uint32_t>(local_alert) * sizeof(uint32_t),
                 0);
  EXPECT_DIF_OK(
      dif_alert_handler_lock_local_alert(&alert_handler_, local_alert));
}

INSTANTIATE_TEST_SUITE_P(
    LockAllLocalAlerts, LocalAlertLockTest,
    testing::Values(kDifAlertHandlerLocalAlertAlertPingFail,
                    kDifAlertHandlerLocalAlertEscalationPingFail,
                    kDifAlertHandlerLocalAlertAlertIntegrityFail,
                    kDifAlertHandlerLocalAlertEscalationIntegrityFail,
                    kDifAlertHandlerLocalAlertBusIntegrityFail,
                    kDifAlertHandlerLocalAlertShadowedUpdateError,
                    kDifAlertHandlerLocalAlertShadowedStorageError));

TEST_F(LocalAlertLockTest, BadArgs) {
  bool is_locked;
  EXPECT_DIF_BADARG(dif_alert_handler_is_local_alert_locked(
      nullptr, kDifAlertHandlerLocalAlertShadowedStorageError, &is_locked));
  EXPECT_DIF_BADARG(dif_alert_handler_is_local_alert_locked(
      &alert_handler_,
      static_cast<dif_alert_handler_local_alert_t>(kLocalAlerts), &is_locked));
  EXPECT_DIF_BADARG(dif_alert_handler_is_local_alert_locked(
      &alert_handler_, kDifAlertHandlerLocalAlertAlertPingFail, nullptr));

  EXPECT_DIF_BADARG(dif_alert_handler_lock_local_alert(
      nullptr, kDifAlertHandlerLocalAlertAlertPingFail));
  EXPECT_DIF_BADARG(dif_alert_handler_lock_local_alert(
      &alert_handler_,
      static_cast<dif_alert_handler_local_alert_t>(kLocalAlerts)));
}

class ClassLockTest : public AlertHandlerTest,
                      public testing::WithParamInterface<
                          std::tuple<dif_alert_handler_class_t, uint32_t>> {};

static std::vector<std::tuple<dif_alert_handler_class_t, uint32_t>>
    class_regwen_pairs{
        std::tuple<dif_alert_handler_class_t, uint32_t>{
            kDifAlertHandlerClassA, ALERT_HANDLER_CLASSA_REGWEN_REG_OFFSET},
        std::tuple<dif_alert_handler_class_t, uint32_t>{
            kDifAlertHandlerClassB, ALERT_HANDLER_CLASSB_REGWEN_REG_OFFSET},
        std::tuple<dif_alert_handler_class_t, uint32_t>{
            kDifAlertHandlerClassC, ALERT_HANDLER_CLASSC_REGWEN_REG_OFFSET},
        std::tuple<dif_alert_handler_class_t, uint32_t>{
            kDifAlertHandlerClassD, ALERT_HANDLER_CLASSD_REGWEN_REG_OFFSET}};

TEST_P(ClassLockTest, IsClassLocked) {
  dif_alert_handler_class_t alert_class = std::get<0>(GetParam());
  uint32_t regwen_offset = std::get<1>(GetParam());
  bool is_locked = true;

  EXPECT_READ32(regwen_offset, ALERT_HANDLER_CLASSA_REGWEN_REG_RESVAL);
  EXPECT_DIF_OK(dif_alert_handler_is_class_locked(&alert_handler_, alert_class,
                                                  &is_locked));
  EXPECT_FALSE(is_locked);

  is_locked = false;
  EXPECT_READ32(regwen_offset, 0);
  EXPECT_DIF_OK(dif_alert_handler_is_class_locked(&alert_handler_, alert_class,
                                                  &is_locked));
  EXPECT_TRUE(is_locked);
}

INSTANTIATE_TEST_SUITE_P(AllClassesLockedAndUnlocked, ClassLockTest,
                         testing::ValuesIn(class_regwen_pairs));

TEST_P(ClassLockTest, LockClass) {
  dif_alert_handler_class_t alert_class = std::get<0>(GetParam());
  uint32_t regwen_offset = std::get<1>(GetParam());

  EXPECT_WRITE32(regwen_offset, 0);
  EXPECT_DIF_OK(dif_alert_handler_lock_class(&alert_handler_, alert_class));
}

INSTANTIATE_TEST_SUITE_P(LockAllClasses, ClassLockTest,
                         testing::ValuesIn(class_regwen_pairs));

TEST_F(ClassLockTest, BadArgs) {
  bool is_locked;
  EXPECT_DIF_BADARG(dif_alert_handler_is_class_locked(
      nullptr, kDifAlertHandlerClassA, &is_locked));
  EXPECT_DIF_BADARG(dif_alert_handler_is_class_locked(
      &alert_handler_, static_cast<dif_alert_handler_class_t>(kClasses),
      &is_locked));
  EXPECT_DIF_BADARG(dif_alert_handler_is_class_locked(
      &alert_handler_, kDifAlertHandlerClassD, nullptr));

  EXPECT_DIF_BADARG(
      dif_alert_handler_lock_class(nullptr, kDifAlertHandlerClassA));
  EXPECT_DIF_BADARG(dif_alert_handler_lock_class(
      &alert_handler_, static_cast<dif_alert_handler_class_t>(kClasses)));
}

class PingTimerLockTest : public AlertHandlerTest {};

TEST_F(PingTimerLockTest, IsPingTimerLocked) {
  bool flag;

  EXPECT_READ32(ALERT_HANDLER_PING_TIMER_REGWEN_REG_OFFSET, 1);
  EXPECT_DIF_OK(dif_alert_handler_is_ping_timer_locked(&alert_handler_, &flag));
  EXPECT_FALSE(flag);

  EXPECT_READ32(ALERT_HANDLER_PING_TIMER_REGWEN_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_alert_handler_is_ping_timer_locked(&alert_handler_, &flag));
  EXPECT_TRUE(flag);
}

TEST_F(PingTimerLockTest, LockPingTimer) {
  EXPECT_WRITE32(ALERT_HANDLER_PING_TIMER_REGWEN_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_alert_handler_lock_ping_timer(&alert_handler_));
}

TEST_F(PingTimerLockTest, NullArgs) {
  bool flag;
  EXPECT_DIF_BADARG(dif_alert_handler_is_ping_timer_locked(nullptr, &flag));
  EXPECT_DIF_BADARG(
      dif_alert_handler_is_ping_timer_locked(&alert_handler_, nullptr));

  EXPECT_DIF_BADARG(dif_alert_handler_lock_ping_timer(nullptr));
}

class AlertCauseTest : public AlertHandlerTest,
                       public testing::WithParamInterface<int> {};

TEST_P(AlertCauseTest, IsCause) {
  dif_alert_handler_alert_t alert = GetParam();
  bool is_cause;

  ptrdiff_t cause_offset =
      ALERT_HANDLER_ALERT_CAUSE_0_REG_OFFSET + alert * sizeof(uint32_t);

  EXPECT_READ32(cause_offset, 0x1);
  EXPECT_DIF_OK(
      dif_alert_handler_alert_is_cause(&alert_handler_, alert, &is_cause));
  EXPECT_TRUE(is_cause);

  EXPECT_READ32(cause_offset, 0x0);
  EXPECT_DIF_OK(
      dif_alert_handler_alert_is_cause(&alert_handler_, alert, &is_cause));
  EXPECT_FALSE(is_cause);
}

INSTANTIATE_TEST_SUITE_P(AllCauses, AlertCauseTest, testing::Range(0, kAlerts));

TEST_P(AlertCauseTest, Ack) {
  dif_alert_handler_alert_t alert = GetParam();

  ptrdiff_t cause_offset =
      ALERT_HANDLER_ALERT_CAUSE_0_REG_OFFSET + alert * sizeof(uint32_t);
  EXPECT_WRITE32(cause_offset, 0x1);
  EXPECT_DIF_OK(dif_alert_handler_alert_acknowledge(&alert_handler_, alert));
}

INSTANTIATE_TEST_SUITE_P(AllAcks, AlertCauseTest, testing::Range(0, kAlerts));

TEST_F(AlertCauseTest, BadAlert) {
  bool is_cause;
  EXPECT_DIF_BADARG(
      dif_alert_handler_alert_is_cause(&alert_handler_, kAlerts, &is_cause));
  EXPECT_DIF_BADARG(
      dif_alert_handler_alert_acknowledge(&alert_handler_, kAlerts));
}

TEST_F(AlertCauseTest, NullArgs) {
  bool is_cause;
  EXPECT_DIF_BADARG(dif_alert_handler_alert_is_cause(nullptr, 5, &is_cause));
  EXPECT_DIF_BADARG(
      dif_alert_handler_alert_is_cause(&alert_handler_, 5, nullptr));
  EXPECT_DIF_BADARG(dif_alert_handler_alert_acknowledge(nullptr, 11));
}

class LocalAlertCauseTest
    : public AlertHandlerTest,
      public testing::WithParamInterface<dif_alert_handler_local_alert_t> {};

TEST_P(LocalAlertCauseTest, IsCause) {
  dif_alert_handler_local_alert_t local_alert = GetParam();
  bool is_cause;

  EXPECT_READ32(ALERT_HANDLER_LOC_ALERT_CAUSE_0_REG_OFFSET +
                    static_cast<uint32_t>(local_alert) * sizeof(uint32_t),
                0x1);
  EXPECT_DIF_OK(dif_alert_handler_local_alert_is_cause(&alert_handler_,
                                                       local_alert, &is_cause));
  EXPECT_TRUE(is_cause);

  EXPECT_READ32(ALERT_HANDLER_LOC_ALERT_CAUSE_0_REG_OFFSET +
                    static_cast<uint32_t>(local_alert) * sizeof(uint32_t),
                0x0);
  EXPECT_DIF_OK(dif_alert_handler_local_alert_is_cause(&alert_handler_,
                                                       local_alert, &is_cause));
  EXPECT_FALSE(is_cause);
}

INSTANTIATE_TEST_SUITE_P(
    AllCauses, LocalAlertCauseTest,
    testing::Values(kDifAlertHandlerLocalAlertAlertPingFail,
                    kDifAlertHandlerLocalAlertEscalationPingFail,
                    kDifAlertHandlerLocalAlertAlertIntegrityFail,
                    kDifAlertHandlerLocalAlertEscalationIntegrityFail,
                    kDifAlertHandlerLocalAlertBusIntegrityFail,
                    kDifAlertHandlerLocalAlertShadowedUpdateError,
                    kDifAlertHandlerLocalAlertShadowedStorageError));

TEST_P(LocalAlertCauseTest, Ack) {
  dif_alert_handler_local_alert_t local_alert = GetParam();

  EXPECT_WRITE32(ALERT_HANDLER_LOC_ALERT_CAUSE_0_REG_OFFSET +
                     static_cast<uint32_t>(local_alert) * sizeof(uint32_t),
                 0x1);
  EXPECT_DIF_OK(
      dif_alert_handler_local_alert_acknowledge(&alert_handler_, local_alert));
}

INSTANTIATE_TEST_SUITE_P(
    AllAcks, LocalAlertCauseTest,
    testing::Values(kDifAlertHandlerLocalAlertAlertPingFail,
                    kDifAlertHandlerLocalAlertEscalationPingFail,
                    kDifAlertHandlerLocalAlertAlertIntegrityFail,
                    kDifAlertHandlerLocalAlertEscalationIntegrityFail,
                    kDifAlertHandlerLocalAlertBusIntegrityFail,
                    kDifAlertHandlerLocalAlertShadowedUpdateError,
                    kDifAlertHandlerLocalAlertShadowedStorageError));

TEST_F(LocalAlertCauseTest, BadLocalAlert) {
  bool is_cause;
  EXPECT_DIF_BADARG(dif_alert_handler_local_alert_is_cause(
      &alert_handler_,
      static_cast<dif_alert_handler_local_alert_t>(kLocalAlerts), &is_cause));
  EXPECT_DIF_BADARG(dif_alert_handler_local_alert_acknowledge(
      &alert_handler_,
      static_cast<dif_alert_handler_local_alert_t>(kLocalAlerts)));
}

TEST_F(LocalAlertCauseTest, NullArgs) {
  bool is_cause;
  EXPECT_DIF_BADARG(dif_alert_handler_local_alert_is_cause(
      nullptr, kDifAlertHandlerLocalAlertEscalationPingFail, &is_cause));
  EXPECT_DIF_BADARG(dif_alert_handler_local_alert_is_cause(
      &alert_handler_, kDifAlertHandlerLocalAlertEscalationPingFail, nullptr));
  EXPECT_DIF_BADARG(dif_alert_handler_local_alert_acknowledge(
      nullptr, kDifAlertHandlerLocalAlertEscalationIntegrityFail));
}

class EscalationTest : public AlertHandlerTest {};

TEST_F(EscalationTest, CanClear) {
  bool can_clear;

  EXPECT_READ32(ALERT_HANDLER_CLASSB_CLR_REGWEN_REG_OFFSET, true);
  EXPECT_DIF_OK(dif_alert_handler_escalation_can_clear(
      &alert_handler_, kDifAlertHandlerClassB, &can_clear));
  EXPECT_TRUE(can_clear);

  EXPECT_READ32(ALERT_HANDLER_CLASSA_CLR_REGWEN_REG_OFFSET, false);
  EXPECT_DIF_OK(dif_alert_handler_escalation_can_clear(
      &alert_handler_, kDifAlertHandlerClassA, &can_clear));
  EXPECT_FALSE(can_clear);
}

TEST_F(EscalationTest, Disable) {
  EXPECT_WRITE32(ALERT_HANDLER_CLASSC_CLR_REGWEN_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_alert_handler_escalation_disable_clearing(
      &alert_handler_, kDifAlertHandlerClassC));
}

TEST_F(EscalationTest, Clear) {
  EXPECT_WRITE32_SHADOWED(ALERT_HANDLER_CLASSD_CLR_SHADOWED_REG_OFFSET, true);
  EXPECT_DIF_OK(dif_alert_handler_escalation_clear(&alert_handler_,
                                                   kDifAlertHandlerClassD));
}

TEST_F(EscalationTest, NullArgs) {
  bool can_clear;

  EXPECT_DIF_BADARG(dif_alert_handler_escalation_can_clear(
      nullptr, kDifAlertHandlerClassB, &can_clear));
  EXPECT_DIF_BADARG(dif_alert_handler_escalation_can_clear(
      &alert_handler_, kDifAlertHandlerClassB, nullptr));
  EXPECT_DIF_BADARG(dif_alert_handler_escalation_disable_clearing(
      nullptr, kDifAlertHandlerClassC));
  EXPECT_DIF_BADARG(
      dif_alert_handler_escalation_clear(nullptr, kDifAlertHandlerClassD));
}

class GetterTest : public AlertHandlerTest {};

TEST_F(GetterTest, GetAcc) {
  uint16_t num_alerts;
  EXPECT_READ32(ALERT_HANDLER_CLASSB_ACCUM_CNT_REG_OFFSET, 0xaaaa);
  EXPECT_DIF_OK(dif_alert_handler_get_accumulator(
      &alert_handler_, kDifAlertHandlerClassB, &num_alerts));
  EXPECT_EQ(num_alerts, 0xaaaa);
}

TEST_F(GetterTest, GetCycles) {
  uint32_t cycles;
  EXPECT_READ32(ALERT_HANDLER_CLASSD_ESC_CNT_REG_OFFSET, 0xaaaaaaaa);
  EXPECT_DIF_OK(dif_alert_handler_get_escalation_counter(
      &alert_handler_, kDifAlertHandlerClassD, &cycles));
  EXPECT_EQ(cycles, 0xaaaaaaaa);
}

TEST_F(GetterTest, GetState) {
  dif_alert_handler_class_state_t state;

  EXPECT_READ32(ALERT_HANDLER_CLASSC_STATE_REG_OFFSET,
                ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_VALUE_TIMEOUT);
  EXPECT_DIF_OK(dif_alert_handler_get_class_state(
      &alert_handler_, kDifAlertHandlerClassC, &state));
  EXPECT_EQ(state, kDifAlertHandlerClassStateTimeout);

  EXPECT_READ32(ALERT_HANDLER_CLASSA_STATE_REG_OFFSET,
                ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_VALUE_PHASE2);
  EXPECT_DIF_OK(dif_alert_handler_get_class_state(
      &alert_handler_, kDifAlertHandlerClassA, &state));
  EXPECT_EQ(state, kDifAlertHandlerClassStatePhase2);
}

TEST_F(GetterTest, NullArgs) {
  uint16_t alerts;
  EXPECT_DIF_BADARG(dif_alert_handler_get_accumulator(
      nullptr, kDifAlertHandlerClassB, &alerts));
  EXPECT_DIF_BADARG(dif_alert_handler_get_accumulator(
      &alert_handler_, kDifAlertHandlerClassB, nullptr));

  uint32_t cycles;
  EXPECT_DIF_BADARG(dif_alert_handler_get_escalation_counter(
      nullptr, kDifAlertHandlerClassB, &cycles));
  EXPECT_DIF_BADARG(dif_alert_handler_get_escalation_counter(
      &alert_handler_, kDifAlertHandlerClassB, nullptr));

  dif_alert_handler_class_state_t state;
  EXPECT_DIF_BADARG(dif_alert_handler_get_class_state(
      nullptr, kDifAlertHandlerClassC, &state));
  EXPECT_DIF_BADARG(dif_alert_handler_get_class_state(
      &alert_handler_, kDifAlertHandlerClassC, nullptr));
}

}  // namespace
}  // namespace dif_alert_handler_unittest
