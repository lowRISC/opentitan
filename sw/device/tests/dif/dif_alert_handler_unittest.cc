// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_alert_handler.h"

#include <cstring>
#include <limits>
#include <ostream>

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/testing/mock_mmio.h"

#include "alert_handler_regs.h"  // Generated.

namespace dif_alert_handler_unittest {
namespace {
using ::mock_mmio::LeInt;
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::_;
using ::testing::Return;

constexpr uint32_t kAlerts = 12;
constexpr uint32_t kAllOnes = std::numeric_limits<uint32_t>::max();

class AlertTest : public testing::Test, public MmioTest {
 protected:
  dif_alert_handler_t handler_ = {.params = {
                                      .base_addr = dev().region(),
                                      .alert_count = kAlerts,
                                      .escalation_signal_count = 4,
                                  }};
};

class InitTest : public AlertTest,
                 public testing::WithParamInterface<uint32_t> {};

TEST_P(InitTest, Success) {
  dif_alert_handler_params_t params = {
      .base_addr = dev().region(),
      .alert_count = GetParam(),
      .escalation_signal_count = 4,
  };

  dif_alert_handler_t handler;
  EXPECT_EQ(dif_alert_handler_init(params, &handler), kDifAlertHandlerOk);
}

TEST_P(InitTest, NullArgs) {
  dif_alert_handler_params_t params = {
      .base_addr = dev().region(),
      .alert_count = GetParam(),
      .escalation_signal_count = 4,
  };

  EXPECT_EQ(dif_alert_handler_init(params, nullptr), kDifAlertHandlerBadArg);
}

INSTANTIATE_TEST_SUITE_P(
    InitTestSignalCounts, InitTest,
    testing::Values(1, 2, 12, 16
                    // TODO: Enable these parameters once we can support them.
                    // See: #3826
                    // 24, 32,
                    ));

class ConfigTest : public AlertTest {
  // We provide our own dev_ member variable in this fixture, in order to
  // support IgnoreMmioCalls().
  //
  // NOTE: This must come before handler_!
 private:
  std::unique_ptr<MockDevice> dev_ =
      std::make_unique<testing::StrictMock<MockDevice>>();

 protected:
  ConfigTest() { handler_.params.base_addr = dev().region(); }
  // Non-virtual-override dev(), so that EXPECT_*() functions look this one
  // up instead of AlertTest::dev().
  MockDevice &dev() { return *dev_; }

  // Disables expectations on MMIO operations. This is useful for configuration
  // tests that partially configure the device but fail due to a configuration
  // error, returning kError.
  void IgnoreMmioCalls() {
    dev_ = std::make_unique<testing::NiceMock<MockDevice>>();
    handler_.params.base_addr = dev().region();

    // Make sure that the peripheral looks unlocked.
    ON_CALL(*dev_, Read32(_)).WillByDefault(Return(kAllOnes));
  }
};

TEST_F(ConfigTest, Locked) {
  dif_alert_handler_config_t config = {
      .ping_timeout = 0,
  };

  EXPECT_READ32(ALERT_HANDLER_REGWEN_REG_OFFSET, 0);

  EXPECT_EQ(dif_alert_handler_configure(&handler_, config),
            kDifAlertHandlerConfigLocked);
}

TEST_F(ConfigTest, NoClassInit) {
  dif_alert_handler_config_t config = {
      .ping_timeout = 50,
  };

  EXPECT_READ32(ALERT_HANDLER_REGWEN_REG_OFFSET,
                {{ALERT_HANDLER_REGWEN_REGWEN_BIT, true}});

  EXPECT_WRITE32(
      ALERT_HANDLER_PING_TIMEOUT_CYC_REG_OFFSET,
      {{ALERT_HANDLER_PING_TIMEOUT_CYC_PING_TIMEOUT_CYC_OFFSET, 50}});

  EXPECT_EQ(dif_alert_handler_configure(&handler_, config),
            kDifAlertHandlerConfigOk);
}

TEST_F(ConfigTest, TimeoutTooBig) {
  dif_alert_handler_config_t config = {
      .ping_timeout = ALERT_HANDLER_PING_TIMEOUT_CYC_PING_TIMEOUT_CYC_MASK + 1,
  };

  EXPECT_EQ(dif_alert_handler_configure(&handler_, config),
            kDifAlertHandlerConfigBadArg);
}

TEST_F(ConfigTest, BadClassPtr) {
  dif_alert_handler_config_t config = {
      .ping_timeout = 50,
      .classes = nullptr,
      .classes_len = 2,
  };

  EXPECT_EQ(dif_alert_handler_configure(&handler_, config),
            kDifAlertHandlerConfigBadArg);
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
          .use_escalation_protocol = kDifAlertHandlerToggleDisabled,
          .automatic_locking = kDifAlertHandlerToggleEnabled,
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
          .use_escalation_protocol = kDifAlertHandlerToggleEnabled,
          .automatic_locking = kDifAlertHandlerToggleDisabled,
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

  EXPECT_READ32(ALERT_HANDLER_REGWEN_REG_OFFSET,
                {{ALERT_HANDLER_REGWEN_REGWEN_BIT, true}});

  // Unfortunately, we can't use EXPECT_MASK for these reads and writes,
  // since there are not sequenced exactly.
  EXPECT_READ32(ALERT_HANDLER_ALERT_EN_REG_OFFSET, 0);
  EXPECT_READ32(ALERT_HANDLER_ALERT_CLASS_REG_OFFSET, kAllOnes);

  EXPECT_WRITE32(ALERT_HANDLER_ALERT_EN_REG_OFFSET, {
                                                        {1, true},
                                                        {2, true},
                                                        {5, true},
                                                    });
  uint32_t reg_a = kAllOnes;
  for (auto alert : alerts_a) {
    reg_a =
        bitfield_field32_write(reg_a, {.mask = 0b11, .index = alert * 2}, 0b00);
  }
  EXPECT_WRITE32(ALERT_HANDLER_ALERT_CLASS_REG_OFFSET, reg_a);

  EXPECT_READ32(ALERT_HANDLER_LOC_ALERT_EN_REG_OFFSET, 0);
  EXPECT_READ32(ALERT_HANDLER_LOC_ALERT_CLASS_REG_OFFSET, kAllOnes);

  EXPECT_WRITE32(ALERT_HANDLER_LOC_ALERT_EN_REG_OFFSET,
                 {
                     {ALERT_HANDLER_LOC_ALERT_EN_EN_LA_1_BIT, true},
                 });
  uint32_t loc_reg_a = kAllOnes;
  loc_reg_a = bitfield_field32_write(
      loc_reg_a,
      {
          .mask = ALERT_HANDLER_LOC_ALERT_CLASS_CLASS_LA_1_MASK,
          .index = ALERT_HANDLER_LOC_ALERT_CLASS_CLASS_LA_1_OFFSET,
      },
      0b00);
  EXPECT_WRITE32(ALERT_HANDLER_LOC_ALERT_CLASS_REG_OFFSET, loc_reg_a);

  EXPECT_WRITE32(ALERT_HANDLER_CLASSA_CTRL_REG_OFFSET,
                 {
                     {ALERT_HANDLER_CLASSA_CTRL_EN_BIT, false},
                     {ALERT_HANDLER_CLASSA_CTRL_LOCK_BIT, true},
                     {ALERT_HANDLER_CLASSA_CTRL_EN_E0_BIT, true},
                     {ALERT_HANDLER_CLASSA_CTRL_MAP_E0_OFFSET, 3},
                     {ALERT_HANDLER_CLASSA_CTRL_EN_E2_BIT, true},
                     {ALERT_HANDLER_CLASSA_CTRL_MAP_E2_OFFSET, 1},
                 });

  EXPECT_WRITE32(ALERT_HANDLER_CLASSA_ACCUM_THRESH_REG_OFFSET, 12);
  EXPECT_WRITE32(ALERT_HANDLER_CLASSA_TIMEOUT_CYC_REG_OFFSET, 30000);

  EXPECT_WRITE32(ALERT_HANDLER_CLASSA_PHASE1_CYC_REG_OFFSET, 20000);
  EXPECT_WRITE32(ALERT_HANDLER_CLASSA_PHASE2_CYC_REG_OFFSET, 15000);

  EXPECT_READ32(ALERT_HANDLER_ALERT_EN_REG_OFFSET, 0);
  EXPECT_READ32(ALERT_HANDLER_ALERT_CLASS_REG_OFFSET, kAllOnes);

  EXPECT_WRITE32(ALERT_HANDLER_ALERT_EN_REG_OFFSET, {
                                                        {9, true},
                                                        {6, true},
                                                        {11, true},
                                                    });
  uint32_t reg_b = kAllOnes;
  for (auto alert : alerts_b) {
    reg_b =
        bitfield_field32_write(reg_b, {.mask = 0b11, .index = alert * 2}, 0b01);
  }
  EXPECT_WRITE32(ALERT_HANDLER_ALERT_CLASS_REG_OFFSET, reg_b);

  EXPECT_READ32(ALERT_HANDLER_LOC_ALERT_EN_REG_OFFSET, 0);
  EXPECT_READ32(ALERT_HANDLER_LOC_ALERT_CLASS_REG_OFFSET, kAllOnes);

  EXPECT_WRITE32(ALERT_HANDLER_LOC_ALERT_EN_REG_OFFSET,
                 {
                     {ALERT_HANDLER_LOC_ALERT_EN_EN_LA_0_BIT, true},
                     {ALERT_HANDLER_LOC_ALERT_EN_EN_LA_2_BIT, true},
                 });
  uint32_t loc_reg_b = kAllOnes;
  loc_reg_b = bitfield_field32_write(
      loc_reg_b,
      {
          .mask = ALERT_HANDLER_LOC_ALERT_CLASS_CLASS_LA_0_MASK,
          .index = ALERT_HANDLER_LOC_ALERT_CLASS_CLASS_LA_0_OFFSET,
      },
      0b01);
  loc_reg_b = bitfield_field32_write(
      loc_reg_b,
      {
          .mask = ALERT_HANDLER_LOC_ALERT_CLASS_CLASS_LA_2_MASK,
          .index = ALERT_HANDLER_LOC_ALERT_CLASS_CLASS_LA_2_OFFSET,
      },
      0b01);
  EXPECT_WRITE32(ALERT_HANDLER_LOC_ALERT_CLASS_REG_OFFSET, loc_reg_b);

  EXPECT_WRITE32(ALERT_HANDLER_CLASSB_CTRL_REG_OFFSET,
                 {
                     {ALERT_HANDLER_CLASSB_CTRL_EN_BIT, true},
                     {ALERT_HANDLER_CLASSB_CTRL_LOCK_BIT, false},
                     {ALERT_HANDLER_CLASSB_CTRL_EN_E1_BIT, true},
                     {ALERT_HANDLER_CLASSB_CTRL_MAP_E1_OFFSET, 0},
                 });

  EXPECT_WRITE32(ALERT_HANDLER_CLASSB_ACCUM_THRESH_REG_OFFSET, 8);
  EXPECT_WRITE32(ALERT_HANDLER_CLASSB_TIMEOUT_CYC_REG_OFFSET, 2000);

  EXPECT_WRITE32(ALERT_HANDLER_CLASSB_PHASE1_CYC_REG_OFFSET, 20000);
  EXPECT_WRITE32(ALERT_HANDLER_CLASSB_PHASE2_CYC_REG_OFFSET, 15000);
  EXPECT_WRITE32(ALERT_HANDLER_CLASSB_PHASE3_CYC_REG_OFFSET, 150000);

  EXPECT_WRITE32(
      ALERT_HANDLER_PING_TIMEOUT_CYC_REG_OFFSET,
      {{ALERT_HANDLER_PING_TIMEOUT_CYC_PING_TIMEOUT_CYC_OFFSET, 50}});

  EXPECT_EQ(dif_alert_handler_configure(&handler_, config),
            kDifAlertHandlerConfigOk);
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
          .use_escalation_protocol = kDifAlertHandlerToggleDisabled,
          .automatic_locking = kDifAlertHandlerToggleEnabled,
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

  EXPECT_EQ(dif_alert_handler_configure(&handler_, config),
            kDifAlertHandlerConfigError);
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
          .use_escalation_protocol = kDifAlertHandlerToggleDisabled,
          .automatic_locking = kDifAlertHandlerToggleEnabled,
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

  EXPECT_EQ(dif_alert_handler_configure(&handler_, config),
            kDifAlertHandlerConfigError);
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
          .use_escalation_protocol = kDifAlertHandlerToggleDisabled,
          .automatic_locking = kDifAlertHandlerToggleEnabled,
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

  EXPECT_EQ(dif_alert_handler_configure(&handler_, config),
            kDifAlertHandlerConfigError);
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
          .use_escalation_protocol = kDifAlertHandlerToggleDisabled,
          .automatic_locking = kDifAlertHandlerToggleEnabled,
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
  EXPECT_EQ(dif_alert_handler_configure(&handler_, config),
            kDifAlertHandlerConfigError);
  classes[0].alerts = alerts_a.data();

  classes[0].local_alerts = nullptr;
  EXPECT_EQ(dif_alert_handler_configure(&handler_, config),
            kDifAlertHandlerConfigError);
  classes[0].local_alerts = locals_a.data();

  classes[0].phase_signals = nullptr;
  EXPECT_EQ(dif_alert_handler_configure(&handler_, config),
            kDifAlertHandlerConfigError);
  classes[0].phase_signals = signals_a.data();

  classes[0].phase_durations = nullptr;
  EXPECT_EQ(dif_alert_handler_configure(&handler_, config),
            kDifAlertHandlerConfigError);
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
      {.phase = kDifAlertHandlerClassStateTerminal, .cycles = 20000},
      {.phase = kDifAlertHandlerClassStatePhase2, .cycles = 15000},
  };

  std::vector<dif_alert_handler_class_config_t> classes = {
      {
          .alert_class = static_cast<dif_alert_handler_class_t>(12),
          .alerts = alerts_a.data(),
          .alerts_len = alerts_a.size(),
          .local_alerts = locals_a.data(),
          .local_alerts_len = locals_a.size(),
          .use_escalation_protocol = kDifAlertHandlerToggleDisabled,
          .automatic_locking = kDifAlertHandlerToggleEnabled,
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

  EXPECT_EQ(dif_alert_handler_configure(&handler_, config),
            kDifAlertHandlerConfigError);
}

TEST_F(ConfigTest, NullArgs) {
  EXPECT_EQ(dif_alert_handler_configure(nullptr, {}),
            kDifAlertHandlerConfigBadArg);
}

class LockTest : public AlertTest {};

TEST_F(LockTest, IsLocked) {
  bool flag;

  EXPECT_READ32(ALERT_HANDLER_REGWEN_REG_OFFSET,
                {{ALERT_HANDLER_REGWEN_REGWEN_BIT, true}});
  EXPECT_EQ(dif_alert_handler_is_locked(&handler_, &flag), kDifAlertHandlerOk);
  EXPECT_FALSE(flag);

  EXPECT_READ32(ALERT_HANDLER_REGWEN_REG_OFFSET,
                {{ALERT_HANDLER_REGWEN_REGWEN_BIT, false}});
  EXPECT_EQ(dif_alert_handler_is_locked(&handler_, &flag), kDifAlertHandlerOk);
  EXPECT_TRUE(flag);
}

TEST_F(LockTest, Lock) {
  EXPECT_WRITE32(ALERT_HANDLER_REGWEN_REG_OFFSET,
                 {{ALERT_HANDLER_REGWEN_REGWEN_BIT, true}});
  EXPECT_EQ(dif_alert_handler_lock(&handler_), kDifAlertHandlerOk);
}

TEST_F(LockTest, NullArgs) {
  bool flag;
  EXPECT_EQ(dif_alert_handler_is_locked(nullptr, &flag),
            kDifAlertHandlerBadArg);
  EXPECT_EQ(dif_alert_handler_is_locked(&handler_, nullptr),
            kDifAlertHandlerBadArg);

  EXPECT_EQ(dif_alert_handler_lock(nullptr), kDifAlertHandlerBadArg);
}

class IrqTest : public AlertTest {};

TEST_F(IrqTest, IsPending) {
  bool flag;

  EXPECT_READ32(ALERT_HANDLER_INTR_STATE_REG_OFFSET,
                {
                    {ALERT_HANDLER_INTR_COMMON_CLASSB_BIT, true},
                    {ALERT_HANDLER_INTR_COMMON_CLASSD_BIT, true},
                });
  EXPECT_EQ(dif_alert_handler_irq_is_pending(&handler_, kDifAlertHandlerClassA,
                                             &flag),
            kDifAlertHandlerOk);
  EXPECT_FALSE(flag);

  EXPECT_READ32(ALERT_HANDLER_INTR_STATE_REG_OFFSET,
                {
                    {ALERT_HANDLER_INTR_COMMON_CLASSB_BIT, true},
                    {ALERT_HANDLER_INTR_COMMON_CLASSD_BIT, true},
                });
  EXPECT_EQ(dif_alert_handler_irq_is_pending(&handler_, kDifAlertHandlerClassB,
                                             &flag),
            kDifAlertHandlerOk);
  EXPECT_TRUE(flag);
}

TEST_F(IrqTest, Ack) {
  EXPECT_MASK32(ALERT_HANDLER_INTR_STATE_REG_OFFSET,
                {{ALERT_HANDLER_INTR_COMMON_CLASSC_BIT, 1, true}});
  EXPECT_EQ(
      dif_alert_handler_irq_acknowledge(&handler_, kDifAlertHandlerClassC),
      kDifAlertHandlerOk);
}

TEST_F(IrqTest, GetEnabled) {
  dif_alert_handler_toggle_t flag;

  EXPECT_READ32(ALERT_HANDLER_INTR_ENABLE_REG_OFFSET,
                {
                    {ALERT_HANDLER_INTR_COMMON_CLASSB_BIT, true},
                    {ALERT_HANDLER_INTR_COMMON_CLASSD_BIT, true},
                });
  EXPECT_EQ(dif_alert_handler_irq_get_enabled(&handler_, kDifAlertHandlerClassA,
                                              &flag),
            kDifAlertHandlerOk);
  EXPECT_EQ(flag, kDifAlertHandlerToggleDisabled);

  EXPECT_READ32(ALERT_HANDLER_INTR_ENABLE_REG_OFFSET,
                {
                    {ALERT_HANDLER_INTR_COMMON_CLASSB_BIT, true},
                    {ALERT_HANDLER_INTR_COMMON_CLASSD_BIT, true},
                });
  EXPECT_EQ(dif_alert_handler_irq_get_enabled(&handler_, kDifAlertHandlerClassB,
                                              &flag),
            kDifAlertHandlerOk);
  EXPECT_EQ(flag, kDifAlertHandlerToggleEnabled);
}

TEST_F(IrqTest, SetEnabled) {
  EXPECT_MASK32(ALERT_HANDLER_INTR_ENABLE_REG_OFFSET,
                {{ALERT_HANDLER_INTR_COMMON_CLASSC_BIT, 1, true}});
  EXPECT_EQ(dif_alert_handler_irq_set_enabled(&handler_, kDifAlertHandlerClassC,
                                              kDifAlertHandlerToggleEnabled),
            kDifAlertHandlerOk);
}

TEST_F(IrqTest, SetDisabled) {
  EXPECT_MASK32(ALERT_HANDLER_INTR_ENABLE_REG_OFFSET,
                {{ALERT_HANDLER_INTR_COMMON_CLASSD_BIT, 1, false}});
  EXPECT_EQ(dif_alert_handler_irq_set_enabled(&handler_, kDifAlertHandlerClassD,
                                              kDifAlertHandlerToggleDisabled),
            kDifAlertHandlerOk);
}

TEST_F(IrqTest, Force) {
  EXPECT_WRITE32(ALERT_HANDLER_INTR_TEST_REG_OFFSET,
                 {{ALERT_HANDLER_INTR_COMMON_CLASSC_BIT, true}});
  EXPECT_EQ(dif_alert_handler_irq_force(&handler_, kDifAlertHandlerClassC),
            kDifAlertHandlerOk);
}

TEST_F(IrqTest, Snapshot) {
  EXPECT_WRITE32(ALERT_HANDLER_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_alert_handler_irq_disable_all(&handler_, nullptr),
            kDifAlertHandlerOk);

  EXPECT_READ32(ALERT_HANDLER_INTR_ENABLE_REG_OFFSET, 0xaa4242aa);
  EXPECT_WRITE32(ALERT_HANDLER_INTR_ENABLE_REG_OFFSET, 0);

  dif_alert_handler_irq_snapshot_t snap;
  EXPECT_EQ(dif_alert_handler_irq_disable_all(&handler_, &snap),
            kDifAlertHandlerOk);

  EXPECT_WRITE32(ALERT_HANDLER_INTR_ENABLE_REG_OFFSET, 0xaa4242aa);
  EXPECT_EQ(dif_alert_handler_irq_restore_all(&handler_, &snap),
            kDifAlertHandlerOk);
}

TEST_F(IrqTest, NullArgs) {
  bool flag;
  EXPECT_EQ(
      dif_alert_handler_irq_is_pending(nullptr, kDifAlertHandlerClassA, &flag),
      kDifAlertHandlerBadArg);
  EXPECT_EQ(dif_alert_handler_irq_is_pending(&handler_, kDifAlertHandlerClassA,
                                             nullptr),
            kDifAlertHandlerBadArg);
  EXPECT_EQ(dif_alert_handler_irq_acknowledge(nullptr, kDifAlertHandlerClassA),
            kDifAlertHandlerBadArg);

  dif_alert_handler_toggle_t toggle;
  EXPECT_EQ(dif_alert_handler_irq_get_enabled(nullptr, kDifAlertHandlerClassA,
                                              &toggle),
            kDifAlertHandlerBadArg);
  EXPECT_EQ(dif_alert_handler_irq_get_enabled(&handler_, kDifAlertHandlerClassA,
                                              nullptr),
            kDifAlertHandlerBadArg);
  EXPECT_EQ(dif_alert_handler_irq_set_enabled(nullptr, kDifAlertHandlerClassA,
                                              kDifAlertHandlerToggleEnabled),
            kDifAlertHandlerBadArg);

  EXPECT_EQ(dif_alert_handler_irq_force(nullptr, kDifAlertHandlerClassA),
            kDifAlertHandlerBadArg);

  dif_alert_handler_irq_snapshot_t snap;
  EXPECT_EQ(dif_alert_handler_irq_disable_all(nullptr, &snap),
            kDifAlertHandlerBadArg);
  EXPECT_EQ(dif_alert_handler_irq_disable_all(nullptr, &snap),
            kDifAlertHandlerBadArg);
  EXPECT_EQ(dif_alert_handler_irq_restore_all(&handler_, nullptr),
            kDifAlertHandlerBadArg);
}

class CauseTest : public AlertTest {};

TEST_F(CauseTest, IsCause) {
  bool flag;

  EXPECT_READ32(ALERT_HANDLER_ALERT_CAUSE_REG_OFFSET, {{0, true}, {5, true}});
  EXPECT_EQ(dif_alert_handler_alert_is_cause(&handler_, 5, &flag),
            kDifAlertHandlerOk);
  EXPECT_TRUE(flag);

  EXPECT_READ32(ALERT_HANDLER_ALERT_CAUSE_REG_OFFSET, {{0, true}, {5, true}});
  EXPECT_EQ(dif_alert_handler_alert_is_cause(&handler_, 6, &flag),
            kDifAlertHandlerOk);
  EXPECT_FALSE(flag);
}

TEST_F(CauseTest, Ack) {
  EXPECT_WRITE32(ALERT_HANDLER_ALERT_CAUSE_REG_OFFSET, {{11, true}});
  EXPECT_EQ(dif_alert_handler_alert_acknowledge(&handler_, 11),
            kDifAlertHandlerOk);
}

TEST_F(CauseTest, BadAlert) {
  bool flag;
  EXPECT_EQ(dif_alert_handler_alert_is_cause(&handler_, kAlerts, &flag),
            kDifAlertHandlerBadArg);
  EXPECT_EQ(dif_alert_handler_alert_acknowledge(&handler_, kAlerts),
            kDifAlertHandlerBadArg);
}

TEST_F(CauseTest, IsCauseLocal) {
  bool flag;

  EXPECT_READ32(ALERT_HANDLER_LOC_ALERT_CAUSE_REG_OFFSET,
                {{ALERT_HANDLER_LOC_ALERT_CAUSE_LA_0_BIT, true},
                 {ALERT_HANDLER_LOC_ALERT_CAUSE_LA_1_BIT, true}});
  EXPECT_EQ(dif_alert_handler_local_alert_is_cause(
                &handler_, kDifAlertHandlerLocalAlertEscalationPingFail, &flag),
            kDifAlertHandlerOk);
  EXPECT_TRUE(flag);

  EXPECT_READ32(ALERT_HANDLER_LOC_ALERT_CAUSE_REG_OFFSET,
                {{ALERT_HANDLER_LOC_ALERT_CAUSE_LA_0_BIT, true},
                 {ALERT_HANDLER_LOC_ALERT_CAUSE_LA_1_BIT, true}});
  EXPECT_EQ(dif_alert_handler_local_alert_is_cause(
                &handler_, kDifAlertHandlerLocalAlertAlertIntegrityFail, &flag),
            kDifAlertHandlerOk);
  EXPECT_FALSE(flag);
}

TEST_F(CauseTest, AckLocal) {
  EXPECT_WRITE32(ALERT_HANDLER_LOC_ALERT_CAUSE_REG_OFFSET,
                 {{ALERT_HANDLER_LOC_ALERT_CAUSE_LA_3_BIT, true}});
  EXPECT_EQ(dif_alert_handler_local_alert_acknowledge(
                &handler_, kDifAlertHandlerLocalAlertEscalationIntegrityFail),
            kDifAlertHandlerOk);
}

TEST_F(CauseTest, NullArgs) {
  bool flag;
  EXPECT_EQ(dif_alert_handler_alert_is_cause(nullptr, 5, &flag),
            kDifAlertHandlerBadArg);
  EXPECT_EQ(dif_alert_handler_alert_is_cause(&handler_, 5, nullptr),
            kDifAlertHandlerBadArg);
  EXPECT_EQ(dif_alert_handler_alert_acknowledge(nullptr, 11),
            kDifAlertHandlerBadArg);
  EXPECT_EQ(dif_alert_handler_local_alert_is_cause(
                nullptr, kDifAlertHandlerLocalAlertEscalationPingFail, &flag),
            kDifAlertHandlerBadArg);
  EXPECT_EQ(
      dif_alert_handler_local_alert_is_cause(
          &handler_, kDifAlertHandlerLocalAlertEscalationPingFail, nullptr),
      kDifAlertHandlerBadArg);
  EXPECT_EQ(dif_alert_handler_local_alert_acknowledge(
                nullptr, kDifAlertHandlerLocalAlertEscalationIntegrityFail),
            kDifAlertHandlerBadArg);
}

class EscalationTest : public AlertTest {};

TEST_F(EscalationTest, CanClear) {
  bool flag;

  EXPECT_READ32(ALERT_HANDLER_CLASSB_REGWEN_REG_OFFSET, true);
  EXPECT_EQ(dif_alert_handler_escalation_can_clear(
                &handler_, kDifAlertHandlerClassB, &flag),
            kDifAlertHandlerOk);
  EXPECT_TRUE(flag);

  EXPECT_READ32(ALERT_HANDLER_CLASSA_REGWEN_REG_OFFSET, false);
  EXPECT_EQ(dif_alert_handler_escalation_can_clear(
                &handler_, kDifAlertHandlerClassA, &flag),
            kDifAlertHandlerOk);
  EXPECT_FALSE(flag);
}

TEST_F(EscalationTest, Disable) {
  EXPECT_WRITE32(ALERT_HANDLER_CLASSC_REGWEN_REG_OFFSET, true);
  EXPECT_EQ(dif_alert_handler_escalation_disable_clearing(
                &handler_, kDifAlertHandlerClassC),
            kDifAlertHandlerOk);
}

TEST_F(EscalationTest, Clear) {
  EXPECT_WRITE32(ALERT_HANDLER_CLASSD_CLR_REG_OFFSET, true);
  EXPECT_EQ(
      dif_alert_handler_escalation_clear(&handler_, kDifAlertHandlerClassD),
      kDifAlertHandlerOk);
}

TEST_F(EscalationTest, NullArgs) {
  bool flag;

  EXPECT_EQ(dif_alert_handler_escalation_can_clear(
                nullptr, kDifAlertHandlerClassB, &flag),
            kDifAlertHandlerBadArg);
  EXPECT_EQ(dif_alert_handler_escalation_can_clear(
                &handler_, kDifAlertHandlerClassB, nullptr),
            kDifAlertHandlerBadArg);
  EXPECT_EQ(dif_alert_handler_escalation_disable_clearing(
                nullptr, kDifAlertHandlerClassC),
            kDifAlertHandlerBadArg);
  EXPECT_EQ(dif_alert_handler_escalation_clear(nullptr, kDifAlertHandlerClassD),
            kDifAlertHandlerBadArg);
}

class GetterTest : public AlertTest {};

TEST_F(GetterTest, GetAcc) {
  uint16_t alerts;
  EXPECT_READ32(ALERT_HANDLER_CLASSB_ACCUM_CNT_REG_OFFSET, 0xaaaa);
  EXPECT_EQ(dif_alert_handler_get_accumulator(&handler_, kDifAlertHandlerClassB,
                                              &alerts),
            kDifAlertHandlerOk);
  EXPECT_EQ(alerts, 0xaaaa);
}

TEST_F(GetterTest, GetCycles) {
  uint32_t cycles;
  EXPECT_READ32(ALERT_HANDLER_CLASSD_ESC_CNT_REG_OFFSET, 0xaaaaaaaa);
  EXPECT_EQ(dif_alert_handler_get_escalation_counter(
                &handler_, kDifAlertHandlerClassD, &cycles),
            kDifAlertHandlerOk);
  EXPECT_EQ(cycles, 0xaaaaaaaa);
}

TEST_F(GetterTest, GetState) {
  dif_alert_handler_class_state_t state;

  EXPECT_READ32(ALERT_HANDLER_CLASSC_STATE_REG_OFFSET,
                ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_VALUE_TIMEOUT);
  EXPECT_EQ(dif_alert_handler_get_class_state(&handler_, kDifAlertHandlerClassC,
                                              &state),
            kDifAlertHandlerOk);
  EXPECT_EQ(state, kDifAlertHandlerClassStateTimeout);

  EXPECT_READ32(ALERT_HANDLER_CLASSA_STATE_REG_OFFSET,
                ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_VALUE_PHASE2);
  EXPECT_EQ(dif_alert_handler_get_class_state(&handler_, kDifAlertHandlerClassA,
                                              &state),
            kDifAlertHandlerOk);
  EXPECT_EQ(state, kDifAlertHandlerClassStatePhase2);
}

TEST_F(GetterTest, NullArgs) {
  uint16_t alerts;
  EXPECT_EQ(dif_alert_handler_get_accumulator(nullptr, kDifAlertHandlerClassB,
                                              &alerts),
            kDifAlertHandlerBadArg);
  EXPECT_EQ(dif_alert_handler_get_accumulator(&handler_, kDifAlertHandlerClassB,
                                              nullptr),
            kDifAlertHandlerBadArg);

  uint32_t cycles;
  EXPECT_EQ(dif_alert_handler_get_escalation_counter(
                nullptr, kDifAlertHandlerClassB, &cycles),
            kDifAlertHandlerBadArg);
  EXPECT_EQ(dif_alert_handler_get_escalation_counter(
                &handler_, kDifAlertHandlerClassB, nullptr),
            kDifAlertHandlerBadArg);

  dif_alert_handler_class_state_t state;
  EXPECT_EQ(dif_alert_handler_get_class_state(nullptr, kDifAlertHandlerClassC,
                                              &state),
            kDifAlertHandlerBadArg);
  EXPECT_EQ(dif_alert_handler_get_class_state(&handler_, kDifAlertHandlerClassC,
                                              nullptr),
            kDifAlertHandlerBadArg);
}

}  // namespace
}  // namespace dif_alert_handler_unittest
