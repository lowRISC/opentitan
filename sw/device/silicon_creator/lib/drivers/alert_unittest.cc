// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/alert.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/silicon_creator/lib/base/mock_abs_mmio.h"

#include "alert_handler_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

namespace alert_unittest {
namespace {

class AlertTest : public mask_rom_test::MaskRomTest {
 protected:
  uint32_t base_ = TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR;
  mask_rom_test::MockAbsMmio mmio_;
};

class InitTest : public AlertTest {};

TEST_F(InitTest, AlertConfigureAlertBadIndex) {
  EXPECT_EQ(alert_configure(ALERT_HANDLER_ALERT_CLASS_MULTIREG_COUNT,
                            kAlertClassA, kAlertEnableNone),
            kErrorAlertBadIndex);
}

TEST_F(InitTest, AlertConfigureAlertBadClass) {
  EXPECT_EQ(alert_configure(0, (alert_class_t)-1, kAlertEnableNone),
            kErrorAlertBadClass);
}

TEST_F(InitTest, AlertConfigureAlertBadEnable) {
  // We expect the alert to get configured as class A, but then to
  // experience an error when evaluating the enable parameter.
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_ALERT_CLASS_0_REG_OFFSET, 0);
  EXPECT_EQ(alert_configure(0, kAlertClassA, (alert_enable_t)-1),
            kErrorAlertBadEnable);
}

TEST_F(InitTest, AlertConfigureAlertClassXNoOperation) {
  EXPECT_EQ(alert_configure(0, kAlertClassX, kAlertEnableNone), kErrorOk);
}

TEST_F(InitTest, LocalAlertConfigureAlertClassXNoOperation) {
  EXPECT_EQ(alert_local_configure(0, kAlertClassX, kAlertEnableNone), kErrorOk);
}

TEST_F(InitTest, AlertConfigure0AsClassA) {
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_ALERT_CLASS_0_REG_OFFSET, 0);
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_ALERT_EN_0_REG_OFFSET, 1);
  EXPECT_EQ(alert_configure(0, kAlertClassA, kAlertEnableEnabled), kErrorOk);
}

TEST_F(InitTest, LocalAlertConfigure0AsClassA) {
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_LOC_ALERT_CLASS_0_REG_OFFSET,
                     0);
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_LOC_ALERT_EN_0_REG_OFFSET, 1);
  EXPECT_EQ(alert_local_configure(0, kAlertClassA, kAlertEnableEnabled),
            kErrorOk);
}

TEST_F(InitTest, AlertConfigure1AsClassB) {
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_ALERT_CLASS_1_REG_OFFSET, 1);
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_ALERT_EN_1_REG_OFFSET, 1);
  EXPECT_EQ(alert_configure(1, kAlertClassB, kAlertEnableEnabled), kErrorOk);
}

TEST_F(InitTest, LocalAlertConfigure1AsClassB) {
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_LOC_ALERT_CLASS_1_REG_OFFSET,
                     1);
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_LOC_ALERT_EN_1_REG_OFFSET, 1);
  EXPECT_EQ(alert_local_configure(1, kAlertClassB, kAlertEnableEnabled),
            kErrorOk);
}

TEST_F(InitTest, AlertConfigure2AsClassC) {
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_ALERT_CLASS_2_REG_OFFSET, 2);
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_ALERT_EN_2_REG_OFFSET, 1);
  EXPECT_EQ(alert_configure(2, kAlertClassC, kAlertEnableEnabled), kErrorOk);
}

TEST_F(InitTest, LocalAlertConfigure2AsClassC) {
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_LOC_ALERT_CLASS_2_REG_OFFSET,
                     2);
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_LOC_ALERT_EN_2_REG_OFFSET, 1);
  EXPECT_EQ(alert_local_configure(2, kAlertClassC, kAlertEnableEnabled),
            kErrorOk);
}

TEST_F(InitTest, AlertConfigure3AsClassDLocked) {
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_ALERT_CLASS_3_REG_OFFSET, 3);
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_ALERT_EN_3_REG_OFFSET, 1);
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_ALERT_REGWEN_3_REG_OFFSET, 0);
  EXPECT_EQ(alert_configure(3, kAlertClassD, kAlertEnableLocked), kErrorOk);
}

TEST_F(InitTest, LocalAlertConfigure3AsClassDLocked) {
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_LOC_ALERT_CLASS_3_REG_OFFSET,
                     3);
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_LOC_ALERT_EN_3_REG_OFFSET, 1);
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_LOC_ALERT_REGWEN_3_REG_OFFSET,
                     0);
  EXPECT_EQ(alert_local_configure(3, kAlertClassD, kAlertEnableLocked),
            kErrorOk);
}

TEST_F(InitTest, AlertConfigureClassXBadClass) {
  alert_class_config_t config{};
  EXPECT_EQ(alert_class_configure(kAlertClassX, &config), kErrorAlertBadClass);
}

TEST_F(InitTest, AlertConfigureClassA) {
  alert_class_config_t config = {
      .enabled = kAlertEnableLocked,
      .escalation = kAlertEscalatePhase3,
      .accum_threshold = 1,
      .timeout_cycles = 2,
      .phase_cycles = {1, 10, 100, 1000},
  };
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_CLASSA_CTRL_REG_OFFSET,
                     {
                         {ALERT_HANDLER_CLASSA_CTRL_EN_BIT, true},
                         {ALERT_HANDLER_CLASSA_CTRL_LOCK_BIT, true},
                         {ALERT_HANDLER_CLASSA_CTRL_EN_E3_BIT, true},
                         {ALERT_HANDLER_CLASSA_CTRL_EN_E2_BIT, true},
                         {ALERT_HANDLER_CLASSA_CTRL_EN_E1_BIT, true},
                         {ALERT_HANDLER_CLASSA_CTRL_EN_E0_BIT, true},
                         {ALERT_HANDLER_CLASSA_CTRL_MAP_E0_OFFSET, 0},
                         {ALERT_HANDLER_CLASSA_CTRL_MAP_E1_OFFSET, 1},
                         {ALERT_HANDLER_CLASSA_CTRL_MAP_E2_OFFSET, 2},
                         {ALERT_HANDLER_CLASSA_CTRL_MAP_E3_OFFSET, 3},
                     });
  EXPECT_ABS_WRITE32(mmio_,
                     base_ + ALERT_HANDLER_CLASSA_ACCUM_THRESH_REG_OFFSET, 1);
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_CLASSA_TIMEOUT_CYC_REG_OFFSET,
                     2);
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_CLASSA_PHASE0_CYC_REG_OFFSET,
                     1);
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_CLASSA_PHASE1_CYC_REG_OFFSET,
                     10);
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_CLASSA_PHASE2_CYC_REG_OFFSET,
                     100);
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_CLASSA_PHASE3_CYC_REG_OFFSET,
                     1000);
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_CLASSA_REGWEN_REG_OFFSET, 0);
  EXPECT_EQ(alert_class_configure(kAlertClassA, &config), kErrorOk);
}

TEST_F(InitTest, AlertConfigureClassB) {
  alert_class_config_t config = {
      .enabled = kAlertEnableEnabled,
      .escalation = kAlertEscalatePhase2,
      .accum_threshold = 1,
      .timeout_cycles = 2,
      .phase_cycles = {1, 10, 100, 1000},
  };
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_CLASSB_CTRL_REG_OFFSET,
                     {
                         {ALERT_HANDLER_CLASSA_CTRL_EN_BIT, true},
                         {ALERT_HANDLER_CLASSA_CTRL_LOCK_BIT, false},
                         {ALERT_HANDLER_CLASSA_CTRL_EN_E3_BIT, false},
                         {ALERT_HANDLER_CLASSA_CTRL_EN_E2_BIT, true},
                         {ALERT_HANDLER_CLASSA_CTRL_EN_E1_BIT, true},
                         {ALERT_HANDLER_CLASSA_CTRL_EN_E0_BIT, true},
                         {ALERT_HANDLER_CLASSA_CTRL_MAP_E0_OFFSET, 0},
                         {ALERT_HANDLER_CLASSA_CTRL_MAP_E1_OFFSET, 1},
                         {ALERT_HANDLER_CLASSA_CTRL_MAP_E2_OFFSET, 2},
                         {ALERT_HANDLER_CLASSA_CTRL_MAP_E3_OFFSET, 3},
                     });
  EXPECT_ABS_WRITE32(mmio_,
                     base_ + ALERT_HANDLER_CLASSB_ACCUM_THRESH_REG_OFFSET, 1);
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_CLASSB_TIMEOUT_CYC_REG_OFFSET,
                     2);
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_CLASSB_PHASE0_CYC_REG_OFFSET,
                     1);
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_CLASSB_PHASE1_CYC_REG_OFFSET,
                     10);
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_CLASSB_PHASE2_CYC_REG_OFFSET,
                     100);
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_CLASSB_PHASE3_CYC_REG_OFFSET,
                     1000);
  EXPECT_EQ(alert_class_configure(kAlertClassB, &config), kErrorOk);
}

TEST_F(InitTest, AlertConfigureClassC) {
  alert_class_config_t config = {
      .enabled = kAlertEnableEnabled,
      .escalation = kAlertEscalatePhase1,
      .accum_threshold = 1,
      .timeout_cycles = 2,
      .phase_cycles = {1, 10, 100, 1000},
  };
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_CLASSC_CTRL_REG_OFFSET,
                     {
                         {ALERT_HANDLER_CLASSA_CTRL_EN_BIT, true},
                         {ALERT_HANDLER_CLASSA_CTRL_LOCK_BIT, false},
                         {ALERT_HANDLER_CLASSA_CTRL_EN_E3_BIT, false},
                         {ALERT_HANDLER_CLASSA_CTRL_EN_E2_BIT, false},
                         {ALERT_HANDLER_CLASSA_CTRL_EN_E1_BIT, true},
                         {ALERT_HANDLER_CLASSA_CTRL_EN_E0_BIT, true},
                         {ALERT_HANDLER_CLASSA_CTRL_MAP_E0_OFFSET, 0},
                         {ALERT_HANDLER_CLASSA_CTRL_MAP_E1_OFFSET, 1},
                         {ALERT_HANDLER_CLASSA_CTRL_MAP_E2_OFFSET, 2},
                         {ALERT_HANDLER_CLASSA_CTRL_MAP_E3_OFFSET, 3},
                     });
  EXPECT_ABS_WRITE32(mmio_,
                     base_ + ALERT_HANDLER_CLASSC_ACCUM_THRESH_REG_OFFSET, 1);
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_CLASSC_TIMEOUT_CYC_REG_OFFSET,
                     2);
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_CLASSC_PHASE0_CYC_REG_OFFSET,
                     1);
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_CLASSC_PHASE1_CYC_REG_OFFSET,
                     10);
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_CLASSC_PHASE2_CYC_REG_OFFSET,
                     100);
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_CLASSC_PHASE3_CYC_REG_OFFSET,
                     1000);
  EXPECT_EQ(alert_class_configure(kAlertClassC, &config), kErrorOk);
}

TEST_F(InitTest, AlertConfigureClassD) {
  alert_class_config_t config = {
      .enabled = kAlertEnableEnabled,
      .escalation = kAlertEscalateNone,
      .accum_threshold = 1,
      .timeout_cycles = 2,
      .phase_cycles = {1, 10, 100, 1000},
  };
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_CLASSD_CTRL_REG_OFFSET,
                     {
                         {ALERT_HANDLER_CLASSA_CTRL_EN_BIT, true},
                         {ALERT_HANDLER_CLASSA_CTRL_LOCK_BIT, false},
                         {ALERT_HANDLER_CLASSA_CTRL_EN_E3_BIT, false},
                         {ALERT_HANDLER_CLASSA_CTRL_EN_E2_BIT, false},
                         {ALERT_HANDLER_CLASSA_CTRL_EN_E1_BIT, false},
                         {ALERT_HANDLER_CLASSA_CTRL_EN_E0_BIT, false},
                         {ALERT_HANDLER_CLASSA_CTRL_MAP_E0_OFFSET, 0},
                         {ALERT_HANDLER_CLASSA_CTRL_MAP_E1_OFFSET, 1},
                         {ALERT_HANDLER_CLASSA_CTRL_MAP_E2_OFFSET, 2},
                         {ALERT_HANDLER_CLASSA_CTRL_MAP_E3_OFFSET, 3},
                     });
  EXPECT_ABS_WRITE32(mmio_,
                     base_ + ALERT_HANDLER_CLASSD_ACCUM_THRESH_REG_OFFSET, 1);
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_CLASSD_TIMEOUT_CYC_REG_OFFSET,
                     2);
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_CLASSD_PHASE0_CYC_REG_OFFSET,
                     1);
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_CLASSD_PHASE1_CYC_REG_OFFSET,
                     10);
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_CLASSD_PHASE2_CYC_REG_OFFSET,
                     100);
  EXPECT_ABS_WRITE32(mmio_, base_ + ALERT_HANDLER_CLASSD_PHASE3_CYC_REG_OFFSET,
                     1000);
  EXPECT_EQ(alert_class_configure(kAlertClassD, &config), kErrorOk);
}

}  // namespace
}  // namespace alert_unittest
