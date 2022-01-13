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
  EXPECT_EQ(
      dif_alert_handler_configure_alert(nullptr, 0, kDifAlertHandlerClassA,
                                        kDifToggleEnabled, kDifToggleDisabled),
      kDifBadArg);

  EXPECT_EQ(dif_alert_handler_configure_alert(
                &alert_handler_, kAlerts, kDifAlertHandlerClassA,
                kDifToggleEnabled, kDifToggleDisabled),
            kDifBadArg);

  EXPECT_EQ(
      dif_alert_handler_configure_alert(
          &alert_handler_, 0, static_cast<dif_alert_handler_class_t>(kClasses),
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
  EXPECT_EQ(dif_alert_handler_configure_local_alert(
                nullptr, kDifAlertHandlerLocalAlertBusIntegrityFail,
                kDifAlertHandlerClassA, kDifToggleEnabled, kDifToggleDisabled),
            kDifBadArg);

  EXPECT_EQ(dif_alert_handler_configure_local_alert(
                &alert_handler_,
                static_cast<dif_alert_handler_local_alert_t>(kLocalAlerts),
                kDifAlertHandlerClassA, kDifToggleEnabled, kDifToggleDisabled),
            kDifBadArg);

  EXPECT_EQ(dif_alert_handler_configure_local_alert(
                &alert_handler_, kDifAlertHandlerLocalAlertAlertPingFail,
                static_cast<dif_alert_handler_class_t>(kClasses),
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

  EXPECT_EQ(dif_alert_handler_configure_class(nullptr, kDifAlertHandlerClassB,
                                              valid_config, kDifToggleEnabled,
                                              kDifToggleDisabled),
            kDifBadArg);

  EXPECT_EQ(
      dif_alert_handler_configure_class(
          &alert_handler_, static_cast<dif_alert_handler_class_t>(kClasses),
          valid_config, kDifToggleEnabled, kDifToggleDisabled),
      kDifBadArg);

  EXPECT_EQ(
      dif_alert_handler_configure_class(
          &alert_handler_, static_cast<dif_alert_handler_class_t>(kClasses),
          valid_config, static_cast<dif_toggle_t>(2), kDifToggleDisabled),
      kDifBadArg);

  EXPECT_EQ(
      dif_alert_handler_configure_class(
          &alert_handler_, static_cast<dif_alert_handler_class_t>(kClasses),
          valid_config, kDifToggleEnabled, static_cast<dif_toggle_t>(2)),
      kDifBadArg);
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
  EXPECT_EQ(
      dif_alert_handler_configure_class(nullptr, kDifAlertHandlerClassB, config,
                                        kDifToggleEnabled, kDifToggleDisabled),
      kDifBadArg);
  config.auto_lock_accumulation_counter = kDifToggleDisabled;

  // Bad escalation_phases array dimension.
  config.escalation_phases_len = 1;
  EXPECT_EQ(
      dif_alert_handler_configure_class(nullptr, kDifAlertHandlerClassB, config,
                                        kDifToggleEnabled, kDifToggleDisabled),
      kDifBadArg);
  config.escalation_phases_len = 0;
  config.escalation_phases = &esc_phase;
  EXPECT_EQ(
      dif_alert_handler_configure_class(nullptr, kDifAlertHandlerClassB, config,
                                        kDifToggleEnabled, kDifToggleDisabled),
      kDifBadArg);
  config.escalation_phases = nullptr;

  // Bad crashdump_escalation_phase.
  config.crashdump_escalation_phase = kDifAlertHandlerClassStateTimeout;
  EXPECT_EQ(
      dif_alert_handler_configure_class(nullptr, kDifAlertHandlerClassB, config,
                                        kDifToggleEnabled, kDifToggleDisabled),
      kDifBadArg);
  config.crashdump_escalation_phase = kDifAlertHandlerClassStateTerminal;
  EXPECT_EQ(
      dif_alert_handler_configure_class(nullptr, kDifAlertHandlerClassB, config,
                                        kDifToggleEnabled, kDifToggleDisabled),
      kDifBadArg);
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
  EXPECT_EQ(
      dif_alert_handler_configure_class(nullptr, kDifAlertHandlerClassB, config,
                                        kDifToggleEnabled, kDifToggleDisabled),
      kDifBadArg);
  esc_phases[0].phase = kDifAlertHandlerClassStatePhase2;

  // Bad signal.
  esc_phases[0].signal = kEscSignals;
  EXPECT_EQ(
      dif_alert_handler_configure_class(nullptr, kDifAlertHandlerClassB, config,
                                        kDifToggleEnabled, kDifToggleDisabled),
      kDifBadArg);
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

  EXPECT_WRITE32_SHADOWED(ALERT_HANDLER_CLASSC_ACCUM_THRESH_SHADOWED_REG_OFFSET,
                          config.accumulator_threshold);

  EXPECT_WRITE32_SHADOWED(ALERT_HANDLER_CLASSC_TIMEOUT_CYC_SHADOWED_REG_OFFSET,
                          config.irq_deadline_cycles);

  EXPECT_WRITE32_SHADOWED(
      ALERT_HANDLER_CLASSC_CRASHDUMP_TRIGGER_SHADOWED_REG_OFFSET, 1);

  EXPECT_EQ(dif_alert_handler_configure_class(
                &alert_handler_, kDifAlertHandlerClassC, config,
                kDifToggleEnabled, kDifToggleDisabled),
            kDifOk);
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

  EXPECT_WRITE32_SHADOWED(ALERT_HANDLER_CLASSC_ACCUM_THRESH_SHADOWED_REG_OFFSET,
                          config.accumulator_threshold);

  EXPECT_WRITE32_SHADOWED(ALERT_HANDLER_CLASSC_TIMEOUT_CYC_SHADOWED_REG_OFFSET,
                          config.irq_deadline_cycles);

  EXPECT_WRITE32_SHADOWED(
      ALERT_HANDLER_CLASSC_CRASHDUMP_TRIGGER_SHADOWED_REG_OFFSET, 1);

  EXPECT_WRITE32(ALERT_HANDLER_CLASSC_REGWEN_REG_OFFSET, 0);

  EXPECT_EQ(dif_alert_handler_configure_class(
                &alert_handler_, kDifAlertHandlerClassC, config,
                kDifToggleEnabled, kDifToggleEnabled),
            kDifOk);
}

class ConfigTest : public AlertHandlerTest {};

TEST_F(ConfigTest, Locked) {
  dif_alert_handler_config_t config = {.alerts = nullptr,
                                       .alert_classes = nullptr,
                                       .alerts_len = 0,
                                       .local_alerts = nullptr,
                                       .local_alert_classes = nullptr,
                                       .local_alerts_len = 0,
                                       .classes = nullptr,
                                       .class_configs = nullptr,
                                       .classes_len = 0,
                                       .ping_timeout = 0};

  EXPECT_READ32(
      ALERT_HANDLER_PING_TIMER_EN_SHADOWED_REG_OFFSET,
      {{ALERT_HANDLER_PING_TIMER_EN_SHADOWED_PING_TIMER_EN_SHADOWED_BIT,
        true}});

  EXPECT_EQ(
      dif_alert_handler_configure(&alert_handler_, config, kDifToggleDisabled),
      kDifLocked);
}

TEST_F(ConfigTest, NoClassInit) {
  dif_alert_handler_config_t config = {.alerts = nullptr,
                                       .alert_classes = nullptr,
                                       .alerts_len = 0,
                                       .local_alerts = nullptr,
                                       .local_alert_classes = nullptr,
                                       .local_alerts_len = 0,
                                       .classes = nullptr,
                                       .class_configs = nullptr,
                                       .classes_len = 0,
                                       .ping_timeout = 50};

  EXPECT_READ32(
      ALERT_HANDLER_PING_TIMER_EN_SHADOWED_REG_OFFSET,
      {{ALERT_HANDLER_PING_TIMER_EN_SHADOWED_PING_TIMER_EN_SHADOWED_BIT,
        false}});

  EXPECT_WRITE32_SHADOWED(
      ALERT_HANDLER_PING_TIMEOUT_CYC_SHADOWED_REG_OFFSET,
      {{ALERT_HANDLER_PING_TIMEOUT_CYC_SHADOWED_PING_TIMEOUT_CYC_SHADOWED_OFFSET,
        50}});

  EXPECT_EQ(
      dif_alert_handler_configure(&alert_handler_, config, kDifToggleDisabled),
      kDifOk);
}

TEST_F(ConfigTest, TimeoutTooBig) {
  dif_alert_handler_config_t config = {
      .alerts = nullptr,
      .alert_classes = nullptr,
      .alerts_len = 0,
      .local_alerts = nullptr,
      .local_alert_classes = nullptr,
      .local_alerts_len = 0,
      .classes = nullptr,
      .class_configs = nullptr,
      .classes_len = 0,
      .ping_timeout =
          ALERT_HANDLER_PING_TIMEOUT_CYC_SHADOWED_PING_TIMEOUT_CYC_SHADOWED_MASK +
          1};

  EXPECT_EQ(
      dif_alert_handler_configure(&alert_handler_, config, kDifToggleDisabled),
      kDifBadArg);
}

TEST_F(ConfigTest, BadClassPtr) {
  dif_alert_handler_config_t config = {
      .alerts = nullptr,
      .alert_classes = nullptr,
      .alerts_len = 0,
      .local_alerts = nullptr,
      .local_alert_classes = nullptr,
      .local_alerts_len = 0,
      .classes = nullptr,
      .class_configs = nullptr,
      .classes_len = 2,
      .ping_timeout = 50,
  };

  EXPECT_EQ(
      dif_alert_handler_configure(&alert_handler_, config, kDifToggleDisabled),
      kDifBadArg);
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
