// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/shutdown.h"

#include <array>

#include "gtest/gtest.h"
#include "sw/device/lib/base/global_mock.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_abs_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/mock_alert.h"
#include "sw/device/silicon_creator/lib/drivers/mock_otp.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

#include "alert_handler_regs.h"
#include "flash_ctrl_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "lc_ctrl_regs.h"
#include "otp_ctrl_regs.h"
#include "rv_core_ibex_regs.h"

namespace shutdown_unittest {

using ::testing::ElementsAre;
using ::testing::Invoke;
using ::testing::Return;
using ::testing::Test;

namespace {

namespace internal {
// Create a mock for internal shutdown functions.
class MockShutdownImpl : public ::global_mock::GlobalMock<MockShutdownImpl> {
 public:
  MOCK_METHOD(void, shutdown_report_error, (rom_error_t));
  MOCK_METHOD(void, shutdown_software_escalate, ());
  MOCK_METHOD(void, shutdown_keymgr_kill, ());
  MOCK_METHOD(void, shutdown_reset, ());
  MOCK_METHOD(void, shutdown_flash_kill, ());
  MOCK_METHOD(void, shutdown_hang, ());
};

}  // namespace internal
using MockShutdownImpl = testing::StrictMock<internal::MockShutdownImpl>;
extern "C" {
void shutdown_report_error(rom_error_t error) {
  return MockShutdownImpl::Instance().shutdown_report_error(error);
}
void shutdown_software_escalate(void) {
  return MockShutdownImpl::Instance().shutdown_software_escalate();
}
void shutdown_keymgr_kill(void) {
  return MockShutdownImpl::Instance().shutdown_keymgr_kill();
}
void shutdown_reset(void) {
  return MockShutdownImpl::Instance().shutdown_reset();
}
void shutdown_flash_kill(void) {
  return MockShutdownImpl::Instance().shutdown_flash_kill();
}
void shutdown_hang(void) {
  return MockShutdownImpl::Instance().shutdown_hang();
}

// Real implementations of the above mocks.
extern void unmocked_shutdown_flash_kill(void);
extern void unmocked_shutdown_software_escalate(void);
}  // extern "C"

constexpr uint32_t Pack32(uint8_t a, uint8_t b, uint8_t c, uint8_t d) {
  uint32_t result = (a << 0) | (b << 8) | (c << 16) | (d << 24);
  return result;
}

#define FULL(name, prod, prodend, dev, rma)                          \
  {                                                                  \
    name, kAlertClass##prod, kAlertClass##prodend, kAlertClass##dev, \
        kAlertClass##rma                                             \
  }

#define CLASSIFY(name, prod, prodend, dev, rma)                     \
  Pack32(kAlertClass##prod, kAlertClass##prodend, kAlertClass##dev, \
         kAlertClass##rma)

// This alert configuration is described in the ROM Shutdown specification:
// https://docs.google.com/document/d/1V8hRvQnJhsvddieJbRHS3azbPZvoBWxfxPZV_0YA1QU/edit#
// Dummy alerts have been added to prevent the tests breaking when new alerts
// are added (see #7183). These lists of alerts and local alerts are for test
// purposes only and may not be complete and/or up to date.
// clang-format off
#define ALERTS(Xmacro) \
      Xmacro("Uart0FatalFault",                C, C, X, X), \
      Xmacro("Uart1FatalFault",                C, C, X, X), \
      Xmacro("Uart2FatalFault",                C, C, X, X), \
      Xmacro("Uart3FatalFault",                C, C, X, X), \
      Xmacro("GpioFatalFault",                 C, C, X, X), \
      Xmacro("SpiDeviceFatalFault",            C, C, X, X), \
      Xmacro("SpiHost0FatalFault",             C, C, X, X), \
      Xmacro("SpiHost1FatalFault",             C, C, X, X), \
      Xmacro("I2c0FatalFault",                 C, C, X, X), \
      Xmacro("I2c1FatalFault",                 C, C, X, X), \
      Xmacro("I2c2FatalFault",                 C, C, X, X), \
      Xmacro("PattgenFatalFault",              C, C, X, X), \
      Xmacro("OtpCtrlFatalMacroError",         A, A, X, X), \
      Xmacro("OtpCtrlFatalCheckError",         A, A, X, X), \
      Xmacro("LcCtrlFatalProgError",           A, A, X, X), \
      Xmacro("LcCtrlFatalStateError",          A, A, X, X), \
      Xmacro("LcCtrlFatalBusIntegError",       A, A, X, X), \
      Xmacro("PwrmgrAonFatalFault",            C, C, X, X), \
      Xmacro("RstmgrAonFatalFault",            C, C, X, X), \
      Xmacro("ClkmgrAonFatalFault",            C, C, X, X), \
      Xmacro("SysrstCtrlAonFatalFault",        C, C, X, X), \
      Xmacro("AdcCtrlAonFatalFault",           C, C, X, X), \
      Xmacro("PwmAonFatalFault",               C, C, X, X), \
      Xmacro("PinmuxAonFatalFault",            C, C, X, X), \
      Xmacro("AonTimerAonFatalFault",          C, C, X, X), \
      Xmacro("SensorCtrlAonRecovAs",           B, B, X, X), \
      Xmacro("SensorCtrlAonRecovCg",           C, C, X, X), \
      Xmacro("SensorCtrlAonRecovGd",           C, C, X, X), \
      Xmacro("SensorCtrlAonRecovTsHi",         C, C, X, X), \
      Xmacro("SensorCtrlAonRecovTsLo",         C, C, X, X), \
      Xmacro("SensorCtrlAonRecovFla",          C, C, X, X), \
      Xmacro("SensorCtrlAonRecovOtp",          C, C, X, X), \
      Xmacro("SensorCtrlAonRecovOt0",          C, C, X, X), \
      Xmacro("SensorCtrlAonRecovOt1",          C, C, X, X), \
      Xmacro("SensorCtrlAonRecovOt2",          C, C, X, X), \
      Xmacro("SensorCtrlAonRecovOt3",          C, C, X, X), \
      Xmacro("SensorCtrlAonRecovOt4",          C, C, X, X), \
      Xmacro("SensorCtrlAonRecovOt5",          C, C, X, X), \
      Xmacro("SramCtrlRetAonFatalIntgError",   B, B, X, X), \
      Xmacro("SramCtrlRetAonFatalParityError", B, B, X, X), \
      Xmacro("FlashCtrlRecovErr",              D, D, X, X), \
      Xmacro("FlashCtrlRecovMpErr",            D, D, X, X), \
      Xmacro("FlashCtrlRecovEccErr",           D, D, X, X), \
      Xmacro("FlashCtrlFatalIntgErr",          A, A, X, X), \
      Xmacro("RvPlicFatalFault",               A, A, X, X), \
      Xmacro("AesRecovCtrlUpdateErr",          D, D, X, X), \
      Xmacro("AesFatalFault",                  A, A, X, X), \
      Xmacro("HmacFatalFault",                 A, A, X, X), \
      Xmacro("KmacFatalFault",                 A, A, X, X), \
      Xmacro("KeymgrFatalFaultErr",            A, A, X, X), \
      Xmacro("KeymgrRecovOperationErr",        D, D, X, X), \
      Xmacro("CsrngFatalAlert",                A, A, X, X), \
      Xmacro("EntropySrcRecovAlert",           D, D, X, X), \
      Xmacro("EntropySrcFatalAlert",           A, A, X, X), \
      Xmacro("Edn0FatalAlert",                 A, A, X, X), \
      Xmacro("Edn1FatalAlert",                 A, A, X, X), \
      Xmacro("SramCtrlMainFatalIntgError",     A, A, X, X), \
      Xmacro("SramCtrlMainFatalParityError",   A, A, X, X), \
      Xmacro("OtbnFatal",                      A, A, X, X), \
      Xmacro("OtbnRecov",                      D, D, X, X), \
      Xmacro("RomCtrlFatal",                   A, A, X, X), \
      Xmacro("Dummy61",                        X, X, X, X), \
      Xmacro("Dummy62",                        X, X, X, X), \
      Xmacro("Dummy63",                        X, X, X, X), \
      Xmacro("Dummy64",                        X, X, X, X), \
      Xmacro("Dummy65",                        X, X, X, X), \
      Xmacro("Dummy66",                        X, X, X, X), \
      Xmacro("Dummy67",                        X, X, X, X), \
      Xmacro("Dummy68",                        X, X, X, X), \
      Xmacro("Dummy69",                        X, X, X, X), \
      Xmacro("Dummy70",                        X, X, X, X), \
      Xmacro("Dummy71",                        X, X, X, X), \
      Xmacro("Dummy72",                        X, X, X, X), \
      Xmacro("Dummy73",                        X, X, X, X), \
      Xmacro("Dummy74",                        X, X, X, X), \
      Xmacro("Dummy75",                        X, X, X, X), \
      Xmacro("Dummy76",                        X, X, X, X), \
      Xmacro("Dummy77",                        X, X, X, X), \
      Xmacro("Dummy78",                        X, X, X, X), \
      Xmacro("Dummy79",                        X, X, X, X)

#define LOC_ALERTS(Xmacro) \
      Xmacro("LocAlertPingFail",               A, A, X, X), \
      Xmacro("LocEscPingFail",                 A, A, X, X), \
      Xmacro("LocAlertIntegrityFail",          A, A, X, X), \
      Xmacro("LocEscIntegrityFail",            A, A, X, X), \
      Xmacro("LocBusIntegrityFail",            A, A, X, X), \
      Xmacro("LocShadowRegUpdateFail",         A, A, X, X), \
      Xmacro("LocShadowRegStorageError",       A, A, X, X), \
      Xmacro("LocDummy7",                      X, X, X, X), \
      Xmacro("LocDummy8",                      X, X, X, X), \
      Xmacro("LocDummy9",                      X, X, X, X), \
      Xmacro("LocDummy10",                     X, X, X, X), \
      Xmacro("LocDummy11",                     X, X, X, X), \
      Xmacro("LocDummy12",                     X, X, X, X), \
      Xmacro("LocDummy13",                     X, X, X, X), \
      Xmacro("LocDummy14",                     X, X, X, X), \
      Xmacro("LocDummy15",                     X, X, X, X),
// clang-format on

struct OtpConfiguration {
  uint32_t rom_error_reporting;
  uint32_t rom_bootstrap_en;
  uint32_t rom_alert_class_en;
  uint32_t rom_alert_escalation;
  uint32_t rom_alert_classification[80];
  uint32_t rom_local_alert_classification[16];
  uint32_t rom_alert_accum_thresh[4];
  uint32_t rom_alert_timeout_cycles[4];
  uint32_t rom_alert_phase_cycles[4][4];
};

struct DefaultAlertClassification {
  const char *name;
  alert_class_t prod;
  alert_class_t prodend;
  alert_class_t dev;
  alert_class_t rma;
};

constexpr OtpConfiguration kOtpConfig = {
    .rom_error_reporting = (uint32_t)kShutdownErrorRedactNone,
    .rom_bootstrap_en = 1,
    .rom_alert_class_en = Pack32(kAlertEnableLocked, kAlertEnableEnabled,
                                 kAlertEnableNone, kAlertEnableNone),
    .rom_alert_escalation = Pack32(kAlertEscalatePhase3, kAlertEscalatePhase3,
                                   kAlertEscalateNone, kAlertEscalateNone),
    .rom_alert_classification = {ALERTS(CLASSIFY)},
    .rom_local_alert_classification = {LOC_ALERTS(CLASSIFY)},
    .rom_alert_accum_thresh = {0, 0, 0, 0},
    .rom_alert_timeout_cycles = {0, 0, 0, 0},
    .rom_alert_phase_cycles =
        {
            {0, 10, 10, 0xFFFFFFFF},  // Class A
            {0, 10, 10, 0xFFFFFFFF},  // Class B
            {0, 0, 0, 0},             // Class C
            {0, 0, 0, 0},             // Class D
        },
};

constexpr DefaultAlertClassification kDefaultAlertClassification[] = {
    ALERTS(FULL),
};
static_assert(ARRAYSIZE(kDefaultAlertClassification) <=
                  (OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_ALERT_CLASSIFICATION_SIZE /
                   4),
              "The default alert classification must be less than or equal to "
              "the number of reserved OTP words");

static_assert(kTopEarlgreyAlertIdLast < ARRAYSIZE(kDefaultAlertClassification),
              "The number of alert sources must be smaller than the alert "
              "classification");

constexpr DefaultAlertClassification kDefaultLocAlertClassification[] = {
    LOC_ALERTS(FULL)};
static_assert(
    ARRAYSIZE(kDefaultLocAlertClassification) <=
        (OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_LOCAL_ALERT_CLASSIFICATION_SIZE / 4),
    "The default local alert classification must be less than or "
    "equal to the number of reserved OTP words");

constexpr alert_class_t kClasses[] = {
    kAlertClassA,
    kAlertClassB,
    kAlertClassC,
    kAlertClassD,
};

alert_enable_t RomAlertClassEnable(alert_class_t cls) {
  // Note: these need to match with `rom_alert_class_en` above.
  switch (cls) {
    case kAlertClassA:
      return kAlertEnableLocked;
    case kAlertClassB:
      return kAlertEnableEnabled;
    case kAlertClassC:
      return kAlertEnableNone;
    case kAlertClassD:
      return kAlertEnableNone;
    // Class X (and all other invalid classes) default to class A's enable
    // status.
    default:
      return kAlertEnableLocked;
  }
}

alert_escalate_t RomAlertClassEscalation(alert_class_t cls) {
  // Note: these need to match with `rom_alert_class_escalation` above.
  switch (cls) {
    case kAlertClassA:
      return kAlertEscalatePhase3;
    case kAlertClassB:
      return kAlertEscalatePhase3;
    case kAlertClassC:
      return kAlertEscalateNone;
    case kAlertClassD:
      return kAlertEscalateNone;
    // Class X (and all other invalid classes) default to class A's escalate
    // setting.
    default:
      return kAlertEscalatePhase3;
  }
}

class ShutdownTest : public rom_test::RomTest {
 protected:
  void SetupOtpReads() {
    // Make OTP reads retrieve their values from `otp_config_`.
    ON_CALL(otp_, read32(::testing::_)).WillByDefault([this](uint32_t address) {
      // Must be aligned and in the SW_CFG partition.
      EXPECT_EQ(address % 4, 0);
      EXPECT_GE(address, OTP_CTRL_PARAM_OWNER_SW_CFG_OFFSET);
      EXPECT_LT(address,
                OTP_CTRL_PARAM_OWNER_SW_CFG_OFFSET + sizeof(this->otp_config_));
      // Convert the address to a word index.
      uint32_t index = (address - OTP_CTRL_PARAM_OWNER_SW_CFG_OFFSET) / 4;
      const uint32_t *words =
          reinterpret_cast<const uint32_t *>(&this->otp_config_);
      return words[index];
    });
  }

  void ExpectClassConfigure() {
    ExpectClassConfigure(0);
    ExpectClassConfigure(1);
    ExpectClassConfigure(2);
    ExpectClassConfigure(3);
  }

  void ExpectClassConfigure(size_t i) {
    alert_class_t expected_cls = kClasses[i];
    EXPECT_CALL(alert_, alert_class_configure(expected_cls, ::testing::_))
        .WillOnce(Invoke([this, i](alert_class_t cls,
                                   const alert_class_config_t *config) {
          alert_class_t expected_cls = kClasses[i];
          // Would like to use testing::FiledsAre, but we need a gtest upgrade
          // for that.
          EXPECT_EQ(cls, expected_cls);
          EXPECT_EQ(config->enabled, RomAlertClassEnable(expected_cls));
          EXPECT_EQ(config->escalation, RomAlertClassEscalation(expected_cls));
          EXPECT_EQ(config->accum_threshold,
                    otp_config_.rom_alert_accum_thresh[i]);
          EXPECT_EQ(config->timeout_cycles,
                    otp_config_.rom_alert_timeout_cycles[i]);
          EXPECT_THAT(config->phase_cycles,
                      ElementsAre(otp_config_.rom_alert_phase_cycles[i][0],
                                  otp_config_.rom_alert_phase_cycles[i][1],
                                  otp_config_.rom_alert_phase_cycles[i][2],
                                  otp_config_.rom_alert_phase_cycles[i][3]));
          return kErrorOk;
        }));
  }

  // Expect a call to `shutdown_finalize`.
  void ExpectFinalize(rom_error_t error) {
    // In the RV32 environment, finalize should never return.
    // In the X86_64 unittest environment, verify that all of the various
    // kill functions were called.
    EXPECT_CALL(shutdown_, shutdown_report_error(error));
    EXPECT_CALL(shutdown_, shutdown_software_escalate());
    EXPECT_CALL(shutdown_, shutdown_keymgr_kill());
    EXPECT_CALL(shutdown_, shutdown_reset());
    EXPECT_CALL(shutdown_, shutdown_flash_kill());
    EXPECT_CALL(shutdown_, shutdown_hang());
  }

  OtpConfiguration otp_config_ = kOtpConfig;
  // Use NiceMock because we aren't interested in the specifics of OTP reads,
  // but we want to mock out calls to otp_read32.
  rom_test::NiceMockOtp otp_;
  MockShutdownImpl shutdown_;
  rom_test::MockAlert alert_;
  rom_test::MockAbsMmio mmio_;
};

TEST_F(ShutdownTest, InitializeProd) {
  SetupOtpReads();
  for (size_t i = 0; i < ALERT_HANDLER_ALERT_CLASS_SHADOWED_MULTIREG_COUNT;
       ++i) {
    const auto &c = kDefaultAlertClassification[i];
    alert_class_t cls = c.prod;
    alert_enable_t en = RomAlertClassEnable(cls);
    EXPECT_CALL(alert_, alert_configure(i, cls, en)).WillOnce(Return(kErrorOk));
  }
  for (size_t i = 0; i < ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_MULTIREG_COUNT;
       ++i) {
    const auto &c = kDefaultLocAlertClassification[i];
    alert_class_t cls = c.prod;
    alert_enable_t en = RomAlertClassEnable(cls);
    EXPECT_CALL(alert_, alert_local_configure(i, cls, en))
        .WillOnce(Return(kErrorOk));
  }
  ExpectClassConfigure();
  EXPECT_EQ(shutdown_init(kLcStateProd), kErrorOk);
}

TEST_F(ShutdownTest, InitializeProdWithAlertError) {
  SetupOtpReads();
  for (size_t i = 0; i < ALERT_HANDLER_ALERT_CLASS_SHADOWED_MULTIREG_COUNT;
       ++i) {
    const auto &c = kDefaultAlertClassification[i];
    alert_class_t cls = c.prod;
    alert_enable_t en = RomAlertClassEnable(cls);
    // Return an error on i zero.  The error should not cause alert
    // configuation to abort early (ie: still expect the rest of the
    // alerts to get configured).
    EXPECT_CALL(alert_, alert_configure(i, cls, en))
        .WillOnce(Return(i == 0 ? kErrorUnknown : kErrorOk));
  }
  for (size_t i = 0; i < ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_MULTIREG_COUNT;
       ++i) {
    const auto &c = kDefaultLocAlertClassification[i];
    alert_class_t cls = c.prod;
    alert_enable_t en = RomAlertClassEnable(cls);
    EXPECT_CALL(alert_, alert_local_configure(i, cls, en))
        .WillOnce(Return(kErrorOk));
  }
  ExpectClassConfigure();
  // We expect to get the error from alert configuration.
  EXPECT_EQ(shutdown_init(kLcStateProd), kErrorUnknown);
}

TEST_F(ShutdownTest, InitializeProdWithLocalAlertError) {
  SetupOtpReads();
  for (size_t i = 0; i < ALERT_HANDLER_ALERT_CLASS_SHADOWED_MULTIREG_COUNT;
       ++i) {
    const auto &c = kDefaultAlertClassification[i];
    alert_class_t cls = c.prod;
    alert_enable_t en = RomAlertClassEnable(cls);
    EXPECT_CALL(alert_, alert_configure(i, cls, en)).WillOnce(Return(kErrorOk));
  }
  for (size_t i = 0; i < ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_MULTIREG_COUNT;
       ++i) {
    const auto &c = kDefaultLocAlertClassification[i];
    alert_class_t cls = c.prod;
    alert_enable_t en = RomAlertClassEnable(cls);
    // Return an error on i zero.  The error should not cause alert
    // configuation to abort early (ie: still expect the rest of the
    // alerts to get configured).
    EXPECT_CALL(alert_, alert_local_configure(i, cls, en))
        .WillOnce(Return(i == 0 ? kErrorUnknown : kErrorOk));
  }
  ExpectClassConfigure();
  // We expect to get the error from alert configuration.
  EXPECT_EQ(shutdown_init(kLcStateProd), kErrorUnknown);
}

TEST_F(ShutdownTest, InitializeProdEnd) {
  SetupOtpReads();
  for (size_t i = 0; i < ALERT_HANDLER_ALERT_CLASS_SHADOWED_MULTIREG_COUNT;
       ++i) {
    const auto &c = kDefaultAlertClassification[i];
    alert_class_t cls = c.prodend;
    alert_enable_t en = RomAlertClassEnable(cls);
    EXPECT_CALL(alert_, alert_configure(i, cls, en)).WillOnce(Return(kErrorOk));
  }
  for (size_t i = 0; i < ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_MULTIREG_COUNT;
       ++i) {
    const auto &c = kDefaultLocAlertClassification[i];
    alert_class_t cls = c.prodend;
    alert_enable_t en = RomAlertClassEnable(cls);
    EXPECT_CALL(alert_, alert_local_configure(i, cls, en))
        .WillOnce(Return(kErrorOk));
  }
  ExpectClassConfigure();
  EXPECT_EQ(shutdown_init(kLcStateProdEnd), kErrorOk);
}

TEST_F(ShutdownTest, InitializeDev) {
  SetupOtpReads();
  for (size_t i = 0; i < ALERT_HANDLER_ALERT_CLASS_SHADOWED_MULTIREG_COUNT;
       ++i) {
    const auto &c = kDefaultAlertClassification[i];
    alert_class_t cls = c.dev;
    alert_enable_t en = RomAlertClassEnable(cls);
    EXPECT_CALL(alert_, alert_configure(i, cls, en)).WillOnce(Return(kErrorOk));
  }
  for (size_t i = 0; i < ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_MULTIREG_COUNT;
       ++i) {
    const auto &c = kDefaultLocAlertClassification[i];
    alert_class_t cls = c.dev;
    alert_enable_t en = RomAlertClassEnable(cls);
    EXPECT_CALL(alert_, alert_local_configure(i, cls, en))
        .WillOnce(Return(kErrorOk));
  }
  ExpectClassConfigure();
  EXPECT_EQ(shutdown_init(kLcStateDev), kErrorOk);
}

TEST_F(ShutdownTest, InitializeRma) {
  SetupOtpReads();
  for (size_t i = 0; i < ALERT_HANDLER_ALERT_CLASS_SHADOWED_MULTIREG_COUNT;
       ++i) {
    const auto &c = kDefaultAlertClassification[i];
    alert_class_t cls = c.rma;
    alert_enable_t en = RomAlertClassEnable(cls);
    EXPECT_CALL(alert_, alert_configure(i, cls, en)).WillOnce(Return(kErrorOk));
  }
  for (size_t i = 0; i < ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_MULTIREG_COUNT;
       ++i) {
    const auto &c = kDefaultLocAlertClassification[i];
    alert_class_t cls = c.rma;
    alert_enable_t en = RomAlertClassEnable(cls);
    EXPECT_CALL(alert_, alert_local_configure(i, cls, en))
        .WillOnce(Return(kErrorOk));
  }
  ExpectClassConfigure();
  EXPECT_EQ(shutdown_init(kLcStateRma), kErrorOk);
}

TEST_F(ShutdownTest, RedactPolicyManufacturing) {
  // Devices in manufacturing or RMA states should not redact errors regardless
  // of the redaction level set by OTP.
  constexpr std::array<uint32_t, 9> kManufacturingStates = {
      LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED0,
      LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED1,
      LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED2,
      LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED3,
      LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED4,
      LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED5,
      LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED6,
      LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED7,
      LC_CTRL_LC_STATE_STATE_VALUE_RMA,
  };
  for (const auto state : kManufacturingStates) {
    EXPECT_ABS_READ32(
        TOP_EARLGREY_LC_CTRL_BASE_ADDR + LC_CTRL_LC_STATE_REG_OFFSET,
        static_cast<uint32_t>(state));
    EXPECT_EQ(shutdown_redact_policy(), kShutdownErrorRedactNone);
  }
}

TEST_F(ShutdownTest, RedactPolicyProduction) {
  // Production states should read redaction level from OTP.
  constexpr std::array<uint32_t, 3> kProductionStates = {
      LC_CTRL_LC_STATE_STATE_VALUE_DEV,
      LC_CTRL_LC_STATE_STATE_VALUE_PROD,
      LC_CTRL_LC_STATE_STATE_VALUE_PROD_END,
  };
  for (const auto state : kProductionStates) {
    EXPECT_ABS_READ32(
        TOP_EARLGREY_LC_CTRL_BASE_ADDR + LC_CTRL_LC_STATE_REG_OFFSET,
        static_cast<uint32_t>(state));
    EXPECT_ABS_READ32(
        TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR +
            OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET +
            OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_ERROR_REPORTING_OFFSET,
        static_cast<uint32_t>(kShutdownErrorRedactModule));
    EXPECT_EQ(shutdown_redact_policy(), kShutdownErrorRedactModule);
  }
}

TEST_F(ShutdownTest, RedactPolicyInvalid) {
  // Invalid states should result in the highest redaction level regardless of
  // the redaction level set by OTP.
  EXPECT_ABS_READ32(
      TOP_EARLGREY_LC_CTRL_BASE_ADDR + LC_CTRL_LC_STATE_REG_OFFSET, 0);
  EXPECT_EQ(shutdown_redact_policy(), kShutdownErrorRedactAll);
}

TEST_F(ShutdownTest, InitializeManufacturing) {
  // OTP reads and alert setup should be skipped in the TEST_UNLOCKED lifecycle
  // states.
  EXPECT_EQ(shutdown_init(kLcStateTest), kErrorOk);
}

class ShutdownDeathTest : public ShutdownTest {};

TEST_F(ShutdownDeathTest, InitializeInvalid) {
  EXPECT_DEATH(
      {
        SetupOtpReads();
        shutdown_init(static_cast<lifecycle_state_t>(0));
      },
      "");
}

TEST(ShutdownModule, RedactErrors) {
  EXPECT_EQ(shutdown_redact(kErrorOk, kShutdownErrorRedactNone), 0);
  EXPECT_EQ(shutdown_redact(kErrorOk, kShutdownErrorRedactError), 0);
  EXPECT_EQ(shutdown_redact(kErrorOk, kShutdownErrorRedactModule), 0);
  EXPECT_EQ(shutdown_redact(kErrorOk, kShutdownErrorRedactAll), 0);

  rom_error_t error = static_cast<rom_error_t>(0xaabbccdd);
  EXPECT_EQ(shutdown_redact(error, kShutdownErrorRedactNone), 0xaabbccdd);
  EXPECT_EQ(shutdown_redact(error, kShutdownErrorRedactError), 0x00bbccdd);
  EXPECT_EQ(shutdown_redact(error, kShutdownErrorRedactModule), 0x000000dd);
  EXPECT_EQ(shutdown_redact(error, kShutdownErrorRedactAll), 0xffffffff);
}

TEST_F(ShutdownTest, ShutdownFinalize) {
  SetupOtpReads();
  ExpectFinalize(kErrorUnknown);
  shutdown_finalize(kErrorUnknown);
}

TEST_F(ShutdownTest, FlashKill) {
  EXPECT_ABS_WRITE32(
      TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR + FLASH_CTRL_DIS_REG_OFFSET, 0);
  unmocked_shutdown_flash_kill();
}

TEST_F(ShutdownTest, ShutdownIfErrorOk) { SHUTDOWN_IF_ERROR(kErrorOk); }

TEST_F(ShutdownTest, ShutdownIfErrorUnknown) {
  EXPECT_DEATH(
      {
        ExpectFinalize(kErrorUnknown);
        SHUTDOWN_IF_ERROR(kErrorUnknown);
      },
      "");
}

TEST_F(ShutdownTest, SoftwareEscalate) {
  EXPECT_ABS_WRITE32(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR +
                         RV_CORE_IBEX_SW_FATAL_ERR_REG_OFFSET,
                     0);
  unmocked_shutdown_software_escalate();
}
}  // namespace
}  // namespace shutdown_unittest
