// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * @file
 * @brief Unit tests for pwr_safety_check_sleep_readiness.
 *
 * ## Test Strategy
 *
 * `pwr_safety_check_sleep_readiness` is a pure read-only function that makes
 * exactly the following MMIO reads (in order) when all classes are idle:
 *
 *   1. CLASS{A,B,C,D}_STATE  (four reads via dif_alert_handler_get_class_state)
 *   2. PWRMGR_FAULT_STATUS   (one read via dif_pwrmgr_fatal_err_code_get_codes)
 *
 * The mock_mmio framework records expected reads/writes and verifies them
 * exactly, so each test precisely specifies which registers are touched and in
 * which order.
 *
 * ## Suite Organisation
 *
 * | Suite                    | Condition tested                             |
 * |--------------------------|----------------------------------------------|
 * | PwrSafetyNullArgTest     | NULL pointer arguments                       |
 * | PwrSafetyAllIdleTest     | All classes idle, no fault → safe            |
 * | PwrSafetyAlertPendingTest| One class is non-idle → AlertPending         |
 * | PwrSafetyFatalFaultTest  | All classes idle, fault latched → FatalPower |
 * | PwrSafetyConvenienceTest | pwr_safety_is_sleep_safe() thin wrapper      |
 *
 * ## Register constants used
 *
 * The generated register header `alert_handler_regs.h` defines:
 *   ALERT_HANDLER_CLASS{A,B,C,D}_STATE_REG_OFFSET
 *   ALERT_HANDLER_CLASS{A,B,C,D}_STATE_CLASS{A,B,C,D}_STATE_FIELD
 *   ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_VALUE_{IDLE,TIMEOUT,PHASE0,...}
 *
 * The generated register header `pwrmgr_regs.h` defines:
 *   PWRMGR_FAULT_STATUS_REG_OFFSET
 */

#include "sw/device/lib/runtime/pwr_safety.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"

// Generated register-header constants used to drive mock expectations.
#include "hw/top/alert_handler_regs.h"
#include "hw/top/pwrmgr_regs.h"

namespace pwr_safety_unittest {
namespace {

using ::mock_mmio::LeInt;
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::_;

// ---------------------------------------------------------------------------
// Helper: the register offset for each class's STATE register.
// The values come from the generated alert_handler_regs.h.
// ---------------------------------------------------------------------------
struct ClassStateReg {
  ptrdiff_t offset;
  bitfield_field32_t field;
};

static const ClassStateReg kClassStateRegs[4] = {
    {ALERT_HANDLER_CLASSA_STATE_REG_OFFSET,
     ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_FIELD},
    {ALERT_HANDLER_CLASSB_STATE_REG_OFFSET,
     ALERT_HANDLER_CLASSB_STATE_CLASSB_STATE_FIELD},
    {ALERT_HANDLER_CLASSC_STATE_REG_OFFSET,
     ALERT_HANDLER_CLASSC_STATE_CLASSC_STATE_FIELD},
    {ALERT_HANDLER_CLASSD_STATE_REG_OFFSET,
     ALERT_HANDLER_CLASSD_STATE_CLASSD_STATE_FIELD},
};

// The hardware encoding for "IDLE" is shared across all classes (the
// generated header uses CLASS{A} as the canonical representative).
static constexpr uint32_t kStateIdle =
    ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_VALUE_IDLE;
static constexpr uint32_t kStateTimeout =
    ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_VALUE_TIMEOUT;
static constexpr uint32_t kStatePhase0 =
    ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_VALUE_PHASE0;
static constexpr uint32_t kStatePhase1 =
    ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_VALUE_PHASE1;
static constexpr uint32_t kStatePhase2 =
    ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_VALUE_PHASE2;
static constexpr uint32_t kStatePhase3 =
    ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_VALUE_PHASE3;
static constexpr uint32_t kStateTerminal =
    ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_VALUE_TERMINAL;
static constexpr uint32_t kStateFsmError =
    ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_VALUE_FSMERROR;

// ---------------------------------------------------------------------------
// Fixture: two independent MockDevice instances — one for the alert handler,
// one for the power manager.  This reflects the real hardware topology.
// ---------------------------------------------------------------------------
class PwrSafetyTest : public ::testing::Test {
 protected:
  // We need two separate mock MMIO regions.
  mock_mmio::MockDevice alert_dev_;
  mock_mmio::MockDevice pwrmgr_dev_;

  dif_alert_handler_t alert_handler_{
      .base_addr = alert_dev_.region(),
  };
  dif_pwrmgr_t pwrmgr_{
      .base_addr = pwrmgr_dev_.region(),
  };

  // Helper: programme all four class-state registers to return `hw_value`,
  // packed into the class's STATE field at the correct bit position.
  void ExpectAllClassesState(uint32_t hw_value) {
    for (int i = 0; i < 4; ++i) {
      uint32_t reg_val = bitfield_field32_write(0, kClassStateRegs[i].field,
                                                hw_value);
      EXPECT_READ32_AT(alert_dev_, kClassStateRegs[i].offset, reg_val);
    }
  }

  // Helper: programme the FAULT_STATUS register.
  void ExpectFaultStatus(uint32_t val) {
    EXPECT_READ32_AT(pwrmgr_dev_, PWRMGR_FAULT_STATUS_REG_OFFSET, val);
  }
};

// ---------------------------------------------------------------------------
// NULL-argument tests.
//
// Both the alert handler and the power manager handles must be non-NULL.
// dif_alert_handler_get_class_state and dif_pwrmgr_fatal_err_code_get_codes
// both return kDifBadArg for NULL; pwr_safety maps this to DifError.
// ---------------------------------------------------------------------------
class PwrSafetyNullArgTest : public PwrSafetyTest {};

TEST_F(PwrSafetyNullArgTest, NullAlertHandlerReturnsDifError) {
  // NULL alert handler: the first DIF call will return kDifBadArg, which the
  // utility maps to kPwrSafetySleepResultDifError.
  EXPECT_EQ(pwr_safety_check_sleep_readiness(nullptr, &pwrmgr_),
            kPwrSafetySleepResultDifError);
}

TEST_F(PwrSafetyNullArgTest, NullPwrmgrReturnsDifError) {
  // All alert classes are idle, but the pwrmgr handle is NULL.
  ExpectAllClassesState(kStateIdle);
  EXPECT_EQ(pwr_safety_check_sleep_readiness(&alert_handler_, nullptr),
            kPwrSafetySleepResultDifError);
}

// ---------------------------------------------------------------------------
// "All idle, no faults" — the only path that returns Safe.
// ---------------------------------------------------------------------------
class PwrSafetyAllIdleTest : public PwrSafetyTest {};

TEST_F(PwrSafetyAllIdleTest, AllIdleNoFault) {
  ExpectAllClassesState(kStateIdle);
  ExpectFaultStatus(0u);
  EXPECT_EQ(pwr_safety_check_sleep_readiness(&alert_handler_, &pwrmgr_),
            kPwrSafetySleepResultSafe);
}

TEST_F(PwrSafetyAllIdleTest, ConvenienceWrapperReturnsTrue) {
  ExpectAllClassesState(kStateIdle);
  ExpectFaultStatus(0u);
  EXPECT_TRUE(pwr_safety_is_sleep_safe(&alert_handler_, &pwrmgr_));
}

// ---------------------------------------------------------------------------
// Alert-pending tests — parameterised over which class is non-idle and which
// non-idle state it reports.
// ---------------------------------------------------------------------------

// A pair of (class index 0..3, hw state encoding).
struct AlertPendingParam {
  int class_idx;       // 0=A, 1=B, 2=C, 3=D
  uint32_t hw_state;   // hardware encoding from alert_handler_regs.h
  const char *label;
};

class PwrSafetyAlertPendingTest
    : public PwrSafetyTest,
      public ::testing::WithParamInterface<AlertPendingParam> {};

TEST_P(PwrSafetyAlertPendingTest, NonIdleClassBlocksSleep) {
  const AlertPendingParam &p = GetParam();

  // Programme all classes: the class under test returns the non-idle state,
  // all preceding classes return Idle.  The function short-circuits on the
  // first non-idle class, so subsequent classes are never read.
  for (int i = 0; i <= p.class_idx; ++i) {
    uint32_t hw_val = (i == p.class_idx) ? p.hw_state : kStateIdle;
    uint32_t reg_val =
        bitfield_field32_write(0, kClassStateRegs[i].field, hw_val);
    EXPECT_READ32_AT(alert_dev_, kClassStateRegs[i].offset, reg_val);
  }
  // The power-manager register is NEVER read when a class is non-idle.

  EXPECT_EQ(pwr_safety_check_sleep_readiness(&alert_handler_, &pwrmgr_),
            kPwrSafetySleepResultAlertPending);
}

TEST_P(PwrSafetyAlertPendingTest, ConvenienceWrapperReturnsFalse) {
  const AlertPendingParam &p = GetParam();
  for (int i = 0; i <= p.class_idx; ++i) {
    uint32_t hw_val = (i == p.class_idx) ? p.hw_state : kStateIdle;
    uint32_t reg_val =
        bitfield_field32_write(0, kClassStateRegs[i].field, hw_val);
    EXPECT_READ32_AT(alert_dev_, kClassStateRegs[i].offset, reg_val);
  }
  EXPECT_FALSE(pwr_safety_is_sleep_safe(&alert_handler_, &pwrmgr_));
}

// Exercise all four classes × six non-idle states (Timeout, Phase0–3,
// Terminal, FsmError).
static const AlertPendingParam kAlertPendingCases[] = {
    // Class A — all non-idle states.
    {0, kStateTimeout, "A-Timeout"},
    {0, kStatePhase0, "A-Phase0"},
    {0, kStatePhase1, "A-Phase1"},
    {0, kStatePhase2, "A-Phase2"},
    {0, kStatePhase3, "A-Phase3"},
    {0, kStateTerminal, "A-Terminal"},
    {0, kStateFsmError, "A-FsmError"},
    // Class B — representative subset.
    {1, kStateTimeout, "B-Timeout"},
    {1, kStatePhase0, "B-Phase0"},
    {1, kStateTerminal, "B-Terminal"},
    // Class C — representative subset.
    {2, kStatePhase1, "C-Phase1"},
    {2, kStateFsmError, "C-FsmError"},
    // Class D — representative subset.
    {3, kStateTimeout, "D-Timeout"},
    {3, kStatePhase3, "D-Phase3"},
    {3, kStateTerminal, "D-Terminal"},
};

INSTANTIATE_TEST_SUITE_P(
    AllClassesAndStates, PwrSafetyAlertPendingTest,
    ::testing::ValuesIn(kAlertPendingCases),
    [](const ::testing::TestParamInfo<AlertPendingParam> &info) {
      return info.param.label;
    });

// ---------------------------------------------------------------------------
// Fatal power-fault tests — all classes idle, but FAULT_STATUS is non-zero.
// ---------------------------------------------------------------------------
class PwrSafetyFatalFaultTest
    : public PwrSafetyTest,
      public ::testing::WithParamInterface<uint32_t> {};

TEST_P(PwrSafetyFatalFaultTest, FaultStatusNonZeroBlocksSleep) {
  ExpectAllClassesState(kStateIdle);
  ExpectFaultStatus(GetParam());
  EXPECT_EQ(pwr_safety_check_sleep_readiness(&alert_handler_, &pwrmgr_),
            kPwrSafetySleepResultFatalPowerError);
}

TEST_P(PwrSafetyFatalFaultTest, ConvenienceWrapperReturnsFalse) {
  ExpectAllClassesState(kStateIdle);
  ExpectFaultStatus(GetParam());
  EXPECT_FALSE(pwr_safety_is_sleep_safe(&alert_handler_, &pwrmgr_));
}

// Bitmask values for each individual fault bit plus combined masks.
INSTANTIATE_TEST_SUITE_P(
    FaultBitmasks, PwrSafetyFatalFaultTest,
    ::testing::Values(
        // Individual bits.
        static_cast<uint32_t>(kDifPwrmgrFatalErrTypeRegfileIntegrity),
        static_cast<uint32_t>(kDifPwrmgrFatalErrTypeEscalationTimeout),
        static_cast<uint32_t>(kDifPwrmgrFatalErrTypeMainPowerGlitch),
        // All bits set simultaneously.
        static_cast<uint32_t>(kDifPwrmgrFatalErrTypeRegfileIntegrity |
                               kDifPwrmgrFatalErrTypeEscalationTimeout |
                               kDifPwrmgrFatalErrTypeMainPowerGlitch)));

// ---------------------------------------------------------------------------
// Ordering guarantee: alert-class check always precedes the fault check.
// If class A is non-idle AND a fault is latched, the result is AlertPending
// (not FatalPowerError), because alert classes are evaluated first.
// ---------------------------------------------------------------------------
class PwrSafetyOrderingTest : public PwrSafetyTest {};

TEST_F(PwrSafetyOrderingTest, AlertPendingTakesPriorityOverFault) {
  // Class A in Phase2: short-circuit immediately.
  uint32_t reg_val = bitfield_field32_write(0, kClassStateRegs[0].field,
                                             kStatePhase2);
  EXPECT_READ32_AT(alert_dev_, kClassStateRegs[0].offset, reg_val);
  // FAULT_STATUS is never read because alert check fires first.

  EXPECT_EQ(pwr_safety_check_sleep_readiness(&alert_handler_, &pwrmgr_),
            kPwrSafetySleepResultAlertPending);
}

// ---------------------------------------------------------------------------
// Simulate the scenario described in the security rationale: a Class A alert
// arrives just before sleep, placing the class in Timeout state.  The check
// must prevent sleep entry.
//
// This is the "primary demonstration scenario" requested in the task.
// ---------------------------------------------------------------------------
class PwrSafetySecurityScenarioTest : public PwrSafetyTest {};

TEST_F(PwrSafetySecurityScenarioTest, ClassATimeoutPreventsLowPowerSleep) {
  // Simulated hardware state:
  //   - Class A FSM: Timeout (IRQ fired, escalation counter ticking).
  //   - Classes B, C, D: Idle.
  //
  // Expected outcome: sleep entry is blocked.
  uint32_t reg_val_a = bitfield_field32_write(
      0, kClassStateRegs[0].field, kStateTimeout);
  EXPECT_READ32_AT(alert_dev_, kClassStateRegs[0].offset, reg_val_a);
  // Short-circuit: B, C, D state regs not read; pwrmgr not read.

  pwr_safety_sleep_result_t result =
      pwr_safety_check_sleep_readiness(&alert_handler_, &pwrmgr_);

  EXPECT_EQ(result, kPwrSafetySleepResultAlertPending)
      << "Class A in Timeout state must prevent sleep entry";
}

TEST_F(PwrSafetySecurityScenarioTest, ClassBEscalationPhase1PreventsSleep) {
  // Class A idle.
  uint32_t reg_a = bitfield_field32_write(0, kClassStateRegs[0].field,
                                           kStateIdle);
  EXPECT_READ32_AT(alert_dev_, kClassStateRegs[0].offset, reg_a);

  // Class B in Phase1 (escalation signal may be asserted).
  uint32_t reg_b = bitfield_field32_write(0, kClassStateRegs[1].field,
                                           kStatePhase1);
  EXPECT_READ32_AT(alert_dev_, kClassStateRegs[1].offset, reg_b);
  // Short-circuit here; C and D not read.

  EXPECT_EQ(pwr_safety_check_sleep_readiness(&alert_handler_, &pwrmgr_),
            kPwrSafetySleepResultAlertPending);
}

TEST_F(PwrSafetySecurityScenarioTest, ClassDTerminalPreventsLowPowerSleep) {
  // Classes A, B, C: Idle.
  for (int i = 0; i < 3; ++i) {
    uint32_t reg = bitfield_field32_write(0, kClassStateRegs[i].field,
                                          kStateIdle);
    EXPECT_READ32_AT(alert_dev_, kClassStateRegs[i].offset, reg);
  }
  // Class D: Terminal (chip is effectively bricked; only reset helps).
  uint32_t reg_d = bitfield_field32_write(0, kClassStateRegs[3].field,
                                           kStateTerminal);
  EXPECT_READ32_AT(alert_dev_, kClassStateRegs[3].offset, reg_d);

  EXPECT_EQ(pwr_safety_check_sleep_readiness(&alert_handler_, &pwrmgr_),
            kPwrSafetySleepResultAlertPending);
}

TEST_F(PwrSafetySecurityScenarioTest,
       EscalationTimeoutFaultWithAllClassesIdlePreventsLowPowerSleep) {
  // All classes idle, but an escalation-timeout fault is latched in the power
  // manager (a previous escalation was not acknowledged in time).
  ExpectAllClassesState(kStateIdle);
  ExpectFaultStatus(
      static_cast<uint32_t>(kDifPwrmgrFatalErrTypeEscalationTimeout));

  EXPECT_EQ(pwr_safety_check_sleep_readiness(&alert_handler_, &pwrmgr_),
            kPwrSafetySleepResultFatalPowerError);
}

}  // namespace
}  // namespace pwr_safety_unittest
