// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/sensor_ctrl.h"

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "sw/device/silicon_creator/lib/base/mock_sec_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/mock_otp.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"
#include "sensor_ctrl_regs.h"

namespace sensor_ctrl_unittest {
namespace {
using ::testing::_;
using ::testing::AnyNumber;
using ::testing::NiceMock;
using ::testing::NotNull;
using ::testing::Return;

constexpr uint32_t kOtpSensorCtrl =
    OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_SENSOR_CTRL_ALERT_CFG_OFFSET;

class SensorCtrlTest : public rom_test::RomTest,
                       public testing::WithParamInterface<lifecycle_state_t> {
 protected:
  void SetupExpectations() {
    ON_CALL(otp_, read32(_)).WillByDefault([](uint32_t addr) {
      // Sensor configuration:
      //  0: Enabled=True  Recov=True
      //  1: Enabled=True  Recov=False
      //  2: Enabled=True  Recov=False
      //  3: Enabled=True  Recov=True
      //  4: Enabled=False Recov=False
      //  5: Enabled=False Recov=False
      //  6: Enabled=False Recov=False
      //  7: Enabled=False Recov=False
      //  The remaining values are zero, which is meaningless for "Enabled", and
      //  translates to Recov=True because of the bit-ops in the configure
      //  function.
      //  8: Enabled=X     Recov=True
      //  9: Enabled=X     Recov=True
      // 10: Enabled=X     Recov=True
      switch (addr) {
        case kOtpSensorCtrl + 0:
          return 0x66969666UL;
        case kOtpSensorCtrl + 4:
          return 0x99999999UL;
        case kOtpSensorCtrl + 8:
          return 0x00000000UL;
        default:
          return 0UL;
      }
    });

    EXPECT_CALL(sec_mmio_,
                Write32(base_ + SENSOR_CTRL_ALERT_EN_0_REG_OFFSET, 6));
    EXPECT_CALL(sec_mmio_,
                Write32(base_ + SENSOR_CTRL_ALERT_EN_1_REG_OFFSET, 6));
    EXPECT_CALL(sec_mmio_,
                Write32(base_ + SENSOR_CTRL_ALERT_EN_2_REG_OFFSET, 6));
    EXPECT_CALL(sec_mmio_,
                Write32(base_ + SENSOR_CTRL_ALERT_EN_3_REG_OFFSET, 6));

    EXPECT_CALL(sec_mmio_,
                Write32(base_ + SENSOR_CTRL_ALERT_EN_4_REG_OFFSET, 9));
    EXPECT_CALL(sec_mmio_,
                Write32(base_ + SENSOR_CTRL_ALERT_EN_5_REG_OFFSET, 9));
    EXPECT_CALL(sec_mmio_,
                Write32(base_ + SENSOR_CTRL_ALERT_EN_6_REG_OFFSET, 9));
    EXPECT_CALL(sec_mmio_,
                Write32(base_ + SENSOR_CTRL_ALERT_EN_7_REG_OFFSET, 9));

    EXPECT_CALL(sec_mmio_,
                Write32(base_ + SENSOR_CTRL_ALERT_EN_8_REG_OFFSET, 0));
    EXPECT_CALL(sec_mmio_,
                Write32(base_ + SENSOR_CTRL_ALERT_EN_9_REG_OFFSET, 0));
    EXPECT_CALL(sec_mmio_,
                Write32(base_ + SENSOR_CTRL_ALERT_EN_10_REG_OFFSET, 0));

    // Expect to see a 1 bit for every Recov=False configuration.
    EXPECT_CALL(sec_mmio_,
                Write32(base_ + SENSOR_CTRL_FATAL_ALERT_EN_REG_OFFSET, 0x0F6));
  }
  uint32_t base_ = TOP_EARLGREY_SENSOR_CTRL_AON_BASE_ADDR;
  rom_test::NiceMockOtp otp_;
  rom_test::MockSecMmio sec_mmio_;
};

TEST_P(SensorCtrlTest, Configure) {
  lifecycle_state_t state = GetParam();
  switch (state) {
    case kLcStateTest:
    case kLcStateRma:
      // The configure function does nothing for Test and RMA states.
      break;
    default:
      // Normal test conditions.
      SetupExpectations();
  }
  EXPECT_EQ(kErrorOk, sensor_ctrl_configure(state));
}

INSTANTIATE_TEST_SUITE_P(LcStates, SensorCtrlTest,
                         testing::Values(kLcStateTest, kLcStateRma, kLcStateDev,
                                         kLcStateProd, kLcStateProdEnd));

}  // namespace
}  // namespace sensor_ctrl_unittest
