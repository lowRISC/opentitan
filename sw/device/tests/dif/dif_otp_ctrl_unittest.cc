// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_otp_ctrl.h"

#include <cstring>
#include <limits>
#include <ostream>

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/testing/mock_mmio.h"

#include "otp_ctrl_regs.h"  // Generated.

namespace dif_otp_ctrl_unittest {
namespace {
using ::mock_mmio::LeInt;
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Each;
using ::testing::ElementsAre;

class OtpTest : public testing::Test, public MmioTest {
 protected:
  dif_otp_ctrl_t otp_ = {.params = {.base_addr = dev().region()}};
};

class InitTest : public OtpTest {};

TEST_F(InitTest, Success) {
  dif_otp_ctrl_params_t params = {
      .base_addr = dev().region(),
  };

  dif_otp_ctrl_t handler;
  EXPECT_EQ(dif_otp_ctrl_init(params, &handler), kDifOtpCtrlOk);
}

TEST_F(InitTest, NullArgs) {
  dif_otp_ctrl_params_t params = {
      .base_addr = dev().region(),
  };

  EXPECT_EQ(dif_otp_ctrl_init(params, nullptr), kDifOtpCtrlBadArg);
}

class ConfigTest : public OtpTest {};

TEST_F(ConfigTest, Basic) {
  dif_otp_ctrl_config_t config = {
      .check_timeout = 100'000,
      .integrity_period_mask = 0x3'ffff,
      .consistency_period_mask = 0x3ff'ffff,
  };

  EXPECT_READ32(OTP_CTRL_CHECK_REGWEN_REG_OFFSET,
                {{OTP_CTRL_CHECK_REGWEN_CHECK_REGWEN_BIT, true}});

  EXPECT_WRITE32(OTP_CTRL_CHECK_TIMEOUT_REG_OFFSET, config.check_timeout);
  EXPECT_WRITE32(OTP_CTRL_INTEGRITY_CHECK_PERIOD_REG_OFFSET,
                 config.integrity_period_mask);
  EXPECT_WRITE32(OTP_CTRL_CONSISTENCY_CHECK_PERIOD_REG_OFFSET,
                 config.consistency_period_mask);

  EXPECT_EQ(dif_otp_ctrl_configure(&otp_, config), kDifOtpCtrlOk);
}

TEST_F(ConfigTest, Locked) {
  EXPECT_READ32(OTP_CTRL_CHECK_REGWEN_REG_OFFSET,
                {{OTP_CTRL_CHECK_REGWEN_CHECK_REGWEN_BIT, false}});

  EXPECT_EQ(dif_otp_ctrl_configure(&otp_, {}), kDifOtpCtrlLockableLocked);
}

TEST_F(ConfigTest, IsConfigLocked) {
  bool flag;

  EXPECT_READ32(OTP_CTRL_CHECK_REGWEN_REG_OFFSET,
                {{OTP_CTRL_CHECK_REGWEN_CHECK_REGWEN_BIT, true}});
  EXPECT_EQ(dif_otp_ctrl_config_is_locked(&otp_, &flag), kDifOtpCtrlOk);
  EXPECT_FALSE(flag);

  EXPECT_READ32(OTP_CTRL_CHECK_REGWEN_REG_OFFSET,
                {{OTP_CTRL_CHECK_REGWEN_CHECK_REGWEN_BIT, false}});
  EXPECT_EQ(dif_otp_ctrl_config_is_locked(&otp_, &flag), kDifOtpCtrlOk);
  EXPECT_TRUE(flag);
}

TEST_F(ConfigTest, LockConfig) {
  EXPECT_WRITE32(OTP_CTRL_CHECK_REGWEN_REG_OFFSET,
                 {{OTP_CTRL_CHECK_REGWEN_CHECK_REGWEN_BIT, true}});
  EXPECT_EQ(dif_otp_ctrl_lock_config(&otp_), kDifOtpCtrlOk);
}

TEST_F(ConfigTest, NullArgs) {
  EXPECT_EQ(dif_otp_ctrl_configure(nullptr, {}), kDifOtpCtrlLockableBadArg);

  bool flag;
  EXPECT_EQ(dif_otp_ctrl_config_is_locked(nullptr, &flag), kDifOtpCtrlBadArg);
  EXPECT_EQ(dif_otp_ctrl_config_is_locked(&otp_, nullptr), kDifOtpCtrlBadArg);

  EXPECT_EQ(dif_otp_ctrl_lock_config(nullptr), kDifOtpCtrlBadArg);
}

class CheckTest : public OtpTest {};

TEST_F(CheckTest, Integrity) {
  EXPECT_READ32(OTP_CTRL_CHECK_REGWEN_REG_OFFSET,
                {{OTP_CTRL_CHECK_REGWEN_CHECK_REGWEN_BIT, true}});
  EXPECT_WRITE32(OTP_CTRL_CHECK_TRIGGER_REG_OFFSET,
                 {{OTP_CTRL_CHECK_TRIGGER_INTEGRITY_BIT, true}});

  EXPECT_EQ(dif_otp_ctrl_check_integrity(&otp_), kDifOtpCtrlLockableOk);
}

TEST_F(CheckTest, Consistency) {
  EXPECT_READ32(OTP_CTRL_CHECK_REGWEN_REG_OFFSET,
                {{OTP_CTRL_CHECK_REGWEN_CHECK_REGWEN_BIT, true}});
  EXPECT_WRITE32(OTP_CTRL_CHECK_TRIGGER_REG_OFFSET,
                 {{OTP_CTRL_CHECK_TRIGGER_CONSISTENCY_BIT, true}});

  EXPECT_EQ(dif_otp_ctrl_check_consistency(&otp_), kDifOtpCtrlLockableOk);
}

TEST_F(CheckTest, Locked) {
  EXPECT_READ32(OTP_CTRL_CHECK_REGWEN_REG_OFFSET,
                {{OTP_CTRL_CHECK_REGWEN_CHECK_REGWEN_BIT, false}});
  EXPECT_EQ(dif_otp_ctrl_check_integrity(&otp_), kDifOtpCtrlLockableLocked);

  EXPECT_READ32(OTP_CTRL_CHECK_REGWEN_REG_OFFSET,
                {{OTP_CTRL_CHECK_REGWEN_CHECK_REGWEN_BIT, false}});
  EXPECT_EQ(dif_otp_ctrl_check_consistency(&otp_), kDifOtpCtrlLockableLocked);
}

TEST_F(CheckTest, NullArgs) {
  EXPECT_EQ(dif_otp_ctrl_check_integrity(nullptr), kDifOtpCtrlLockableBadArg);
  EXPECT_EQ(dif_otp_ctrl_check_consistency(nullptr), kDifOtpCtrlLockableBadArg);
}

class ReadLockTest : public OtpTest {};

TEST_F(ReadLockTest, IsLocked) {
  bool flag;

  EXPECT_READ32(
      OTP_CTRL_CREATOR_SW_CFG_READ_LOCK_REG_OFFSET,
      {{OTP_CTRL_CREATOR_SW_CFG_READ_LOCK_CREATOR_SW_CFG_READ_LOCK_BIT, true}});
  EXPECT_EQ(dif_otp_ctrl_reading_is_locked(
                &otp_, kDifOtpCtrlPartitionCreatorSwCfg, &flag),
            kDifOtpCtrlOk);
  EXPECT_FALSE(flag);

  EXPECT_READ32(
      OTP_CTRL_CREATOR_SW_CFG_READ_LOCK_REG_OFFSET,
      {{OTP_CTRL_CREATOR_SW_CFG_READ_LOCK_CREATOR_SW_CFG_READ_LOCK_BIT,
        false}});
  EXPECT_EQ(dif_otp_ctrl_reading_is_locked(
                &otp_, kDifOtpCtrlPartitionCreatorSwCfg, &flag),
            kDifOtpCtrlOk);
  EXPECT_TRUE(flag);

  EXPECT_READ32(
      OTP_CTRL_OWNER_SW_CFG_READ_LOCK_REG_OFFSET,
      {{OTP_CTRL_CREATOR_SW_CFG_READ_LOCK_CREATOR_SW_CFG_READ_LOCK_BIT, true}});
  EXPECT_EQ(dif_otp_ctrl_reading_is_locked(
                &otp_, kDifOtpCtrlPartitionOwnerSwCfg, &flag),
            kDifOtpCtrlOk);
  EXPECT_FALSE(flag);

  EXPECT_READ32(
      OTP_CTRL_OWNER_SW_CFG_READ_LOCK_REG_OFFSET,
      {{OTP_CTRL_CREATOR_SW_CFG_READ_LOCK_CREATOR_SW_CFG_READ_LOCK_BIT,
        false}});
  EXPECT_EQ(dif_otp_ctrl_reading_is_locked(
                &otp_, kDifOtpCtrlPartitionOwnerSwCfg, &flag),
            kDifOtpCtrlOk);
  EXPECT_TRUE(flag);
}

TEST_F(ReadLockTest, Lock) {
  EXPECT_WRITE32(
      OTP_CTRL_CREATOR_SW_CFG_READ_LOCK_REG_OFFSET,
      {{OTP_CTRL_CREATOR_SW_CFG_READ_LOCK_CREATOR_SW_CFG_READ_LOCK_BIT, true}});
  EXPECT_EQ(dif_otp_ctrl_lock_reading(&otp_, kDifOtpCtrlPartitionCreatorSwCfg),
            kDifOtpCtrlOk);

  EXPECT_WRITE32(
      OTP_CTRL_OWNER_SW_CFG_READ_LOCK_REG_OFFSET,
      {{OTP_CTRL_CREATOR_SW_CFG_READ_LOCK_CREATOR_SW_CFG_READ_LOCK_BIT, true}});
  EXPECT_EQ(dif_otp_ctrl_lock_reading(&otp_, kDifOtpCtrlPartitionOwnerSwCfg),
            kDifOtpCtrlOk);
}

TEST_F(ReadLockTest, HwPartition) {
  bool flag;
  EXPECT_EQ(dif_otp_ctrl_lock_reading(&otp_, kDifOtpCtrlPartitionHwCfg),
            kDifOtpCtrlBadArg);
  EXPECT_EQ(
      dif_otp_ctrl_reading_is_locked(&otp_, kDifOtpCtrlPartitionSecret0, &flag),
      kDifOtpCtrlBadArg);
}

TEST_F(ReadLockTest, NullArgs) {
  bool flag;
  EXPECT_EQ(dif_otp_ctrl_reading_is_locked(
                nullptr, kDifOtpCtrlPartitionOwnerSwCfg, &flag),
            kDifOtpCtrlBadArg);
  EXPECT_EQ(dif_otp_ctrl_reading_is_locked(
                &otp_, kDifOtpCtrlPartitionOwnerSwCfg, nullptr),
            kDifOtpCtrlBadArg);

  EXPECT_EQ(dif_otp_ctrl_lock_reading(nullptr, kDifOtpCtrlPartitionOwnerSwCfg),
            kDifOtpCtrlBadArg);
}

class IrqTest : public OtpTest {};

TEST_F(IrqTest, IsPending) {
  bool flag;

  EXPECT_READ32(OTP_CTRL_INTR_STATE_REG_OFFSET,
                {
                    {OTP_CTRL_INTR_COMMON_OTP_ERROR_BIT, true},
                });
  EXPECT_EQ(dif_otp_ctrl_irq_is_pending(&otp_, kDifOtpCtrlIrqDone, &flag),
            kDifOtpCtrlOk);
  EXPECT_FALSE(flag);

  EXPECT_READ32(OTP_CTRL_INTR_STATE_REG_OFFSET,
                {
                    {OTP_CTRL_INTR_COMMON_OTP_ERROR_BIT, true},
                });
  EXPECT_EQ(dif_otp_ctrl_irq_is_pending(&otp_, kDifOtpCtrlIrqError, &flag),
            kDifOtpCtrlOk);
  EXPECT_TRUE(flag);
}

TEST_F(IrqTest, Ack) {
  EXPECT_WRITE32(OTP_CTRL_INTR_STATE_REG_OFFSET,
                 {{OTP_CTRL_INTR_COMMON_OTP_OPERATION_DONE_BIT, true}});
  EXPECT_EQ(dif_otp_ctrl_irq_acknowledge(&otp_, kDifOtpCtrlIrqDone),
            kDifOtpCtrlOk);
}

TEST_F(IrqTest, GetEnabled) {
  dif_otp_ctrl_toggle_t flag;

  EXPECT_READ32(OTP_CTRL_INTR_ENABLE_REG_OFFSET,
                {
                    {OTP_CTRL_INTR_COMMON_OTP_ERROR_BIT, true},
                });
  EXPECT_EQ(dif_otp_ctrl_irq_get_enabled(&otp_, kDifOtpCtrlIrqDone, &flag),
            kDifOtpCtrlOk);
  EXPECT_EQ(flag, kDifOtpCtrlToggleDisabled);

  EXPECT_READ32(OTP_CTRL_INTR_ENABLE_REG_OFFSET,
                {
                    {OTP_CTRL_INTR_COMMON_OTP_ERROR_BIT, true},
                });
  EXPECT_EQ(dif_otp_ctrl_irq_get_enabled(&otp_, kDifOtpCtrlIrqError, &flag),
            kDifOtpCtrlOk);
  EXPECT_EQ(flag, kDifOtpCtrlToggleEnabled);
}

TEST_F(IrqTest, SetEnabled) {
  EXPECT_MASK32(OTP_CTRL_INTR_ENABLE_REG_OFFSET,
                {{OTP_CTRL_INTR_COMMON_OTP_OPERATION_DONE_BIT, 1, true}});
  EXPECT_EQ(dif_otp_ctrl_irq_set_enabled(&otp_, kDifOtpCtrlIrqDone,
                                         kDifOtpCtrlToggleEnabled),
            kDifOtpCtrlOk);
}

TEST_F(IrqTest, SetDisabled) {
  EXPECT_MASK32(OTP_CTRL_INTR_ENABLE_REG_OFFSET,
                {{OTP_CTRL_INTR_COMMON_OTP_ERROR_BIT, 1, false}});
  EXPECT_EQ(dif_otp_ctrl_irq_set_enabled(&otp_, kDifOtpCtrlIrqError,
                                         kDifOtpCtrlToggleDisabled),
            kDifOtpCtrlOk);
}

TEST_F(IrqTest, Force) {
  EXPECT_WRITE32(OTP_CTRL_INTR_TEST_REG_OFFSET,
                 {{OTP_CTRL_INTR_COMMON_OTP_OPERATION_DONE_BIT, true}});
  EXPECT_EQ(dif_otp_ctrl_irq_force(&otp_, kDifOtpCtrlIrqDone), kDifOtpCtrlOk);
}

TEST_F(IrqTest, Snapshot) {
  EXPECT_WRITE32(OTP_CTRL_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_EQ(dif_otp_ctrl_irq_disable_all(&otp_, nullptr), kDifOtpCtrlOk);

  EXPECT_READ32(OTP_CTRL_INTR_ENABLE_REG_OFFSET, 0xaa4242aa);
  EXPECT_WRITE32(OTP_CTRL_INTR_ENABLE_REG_OFFSET, 0);

  dif_otp_ctrl_irq_snapshot_t snap;
  EXPECT_EQ(dif_otp_ctrl_irq_disable_all(&otp_, &snap), kDifOtpCtrlOk);

  EXPECT_WRITE32(OTP_CTRL_INTR_ENABLE_REG_OFFSET, 0xaa4242aa);
  EXPECT_EQ(dif_otp_ctrl_irq_restore_all(&otp_, &snap), kDifOtpCtrlOk);
}

TEST_F(IrqTest, NullArgs) {
  bool flag;
  EXPECT_EQ(dif_otp_ctrl_irq_is_pending(nullptr, kDifOtpCtrlIrqDone, &flag),
            kDifOtpCtrlBadArg);
  EXPECT_EQ(dif_otp_ctrl_irq_is_pending(&otp_, kDifOtpCtrlIrqDone, nullptr),
            kDifOtpCtrlBadArg);
  EXPECT_EQ(dif_otp_ctrl_irq_acknowledge(nullptr, kDifOtpCtrlIrqDone),
            kDifOtpCtrlBadArg);

  dif_otp_ctrl_toggle_t toggle;
  EXPECT_EQ(dif_otp_ctrl_irq_get_enabled(nullptr, kDifOtpCtrlIrqDone, &toggle),
            kDifOtpCtrlBadArg);
  EXPECT_EQ(dif_otp_ctrl_irq_get_enabled(&otp_, kDifOtpCtrlIrqDone, nullptr),
            kDifOtpCtrlBadArg);
  EXPECT_EQ(dif_otp_ctrl_irq_set_enabled(nullptr, kDifOtpCtrlIrqDone,
                                         kDifOtpCtrlToggleEnabled),
            kDifOtpCtrlBadArg);

  EXPECT_EQ(dif_otp_ctrl_irq_force(nullptr, kDifOtpCtrlIrqDone),
            kDifOtpCtrlBadArg);

  dif_otp_ctrl_irq_snapshot_t snap;
  EXPECT_EQ(dif_otp_ctrl_irq_disable_all(nullptr, &snap), kDifOtpCtrlBadArg);
  EXPECT_EQ(dif_otp_ctrl_irq_disable_all(nullptr, &snap), kDifOtpCtrlBadArg);
  EXPECT_EQ(dif_otp_ctrl_irq_restore_all(&otp_, nullptr), kDifOtpCtrlBadArg);
}

class StatusTest : public OtpTest {};

TEST_F(StatusTest, Idle) {
  dif_otp_ctrl_status_t status;

  EXPECT_READ32(OTP_CTRL_STATUS_REG_OFFSET,
                {{OTP_CTRL_STATUS_DAI_IDLE_BIT, true}});
  EXPECT_READ32(OTP_CTRL_ERR_CODE_REG_OFFSET, 0);
  EXPECT_EQ(dif_otp_ctrl_get_status(&otp_, &status), kDifOtpCtrlOk);

  EXPECT_EQ(status.codes, 1 << kDifOtpCtrlStatusCodeDaiIdle);
  EXPECT_THAT(status.causes, Each(kDifOtpCtrlErrorOk));
}

TEST_F(StatusTest, Errors) {
  dif_otp_ctrl_status_t status;

  EXPECT_READ32(OTP_CTRL_STATUS_REG_OFFSET,
                {
                    {OTP_CTRL_STATUS_DAI_IDLE_BIT, true},
                    {OTP_CTRL_STATUS_HW_CFG_ERROR_BIT, true},
                    {OTP_CTRL_STATUS_LCI_ERROR_BIT, true},
                });

  EXPECT_READ32(OTP_CTRL_ERR_CODE_REG_OFFSET,
                {{OTP_CTRL_ERR_CODE_ERR_CODE_2_OFFSET,
                  OTP_CTRL_ERR_CODE_ERR_CODE_0_VALUE_MACRO_ECC_CORR_ERROR},
                 {OTP_CTRL_ERR_CODE_ERR_CODE_8_OFFSET,
                  OTP_CTRL_ERR_CODE_ERR_CODE_0_VALUE_MACRO_ERROR}});

  EXPECT_EQ(dif_otp_ctrl_get_status(&otp_, &status), kDifOtpCtrlOk);
  EXPECT_EQ(status.codes, (1 << kDifOtpCtrlStatusCodeDaiIdle) |
                              (1 << kDifOtpCtrlStatusCodeHwCfgError) |
                              (1 << kDifOtpCtrlStatusCodeLciError));
  EXPECT_EQ(status.causes[kDifOtpCtrlStatusCodeHwCfgError],
            kDifOtpCtrlErrorMacroRecoverableRead);
  EXPECT_EQ(status.causes[kDifOtpCtrlStatusCodeLciError],
            kDifOtpCtrlErrorMacroUnspecified);
}

TEST_F(StatusTest, NullArgs) {
  dif_otp_ctrl_status_t status;

  EXPECT_EQ(dif_otp_ctrl_get_status(nullptr, &status), kDifOtpCtrlBadArg);
  EXPECT_EQ(dif_otp_ctrl_get_status(&otp_, nullptr), kDifOtpCtrlBadArg);
}

class DaiReadTest : public OtpTest {};

TEST_F(DaiReadTest, Read32) {
  EXPECT_READ32(
      OTP_CTRL_DIRECT_ACCESS_REGWEN_REG_OFFSET,
      {{OTP_CTRL_DIRECT_ACCESS_REGWEN_DIRECT_ACCESS_REGWEN_BIT, true}});
  EXPECT_WRITE32(OTP_CTRL_DIRECT_ACCESS_ADDRESS_REG_OFFSET, 0x620);
  EXPECT_WRITE32(OTP_CTRL_DIRECT_ACCESS_CMD_REG_OFFSET,
                 {{OTP_CTRL_DIRECT_ACCESS_CMD_RD_BIT, true}});

  EXPECT_EQ(dif_otp_ctrl_dai_read_start(&otp_, kDifOtpCtrlPartitionHwCfg,
                                        /*address=*/0x20),
            kDifOtpCtrlDaiOk);

  EXPECT_READ32(
      OTP_CTRL_DIRECT_ACCESS_REGWEN_REG_OFFSET,
      {{OTP_CTRL_DIRECT_ACCESS_REGWEN_DIRECT_ACCESS_REGWEN_BIT, true}});
  EXPECT_READ32(OTP_CTRL_DIRECT_ACCESS_RDATA_0_REG_OFFSET, 0x12345678);

  uint32_t val;
  EXPECT_EQ(dif_otp_ctrl_dai_read32_end(&otp_, &val), kDifOtpCtrlDaiOk);
  EXPECT_EQ(val, 0x12345678);
}

TEST_F(DaiReadTest, Read64) {
  EXPECT_READ32(
      OTP_CTRL_DIRECT_ACCESS_REGWEN_REG_OFFSET,
      {{OTP_CTRL_DIRECT_ACCESS_REGWEN_DIRECT_ACCESS_REGWEN_BIT, true}});
  EXPECT_WRITE32(OTP_CTRL_DIRECT_ACCESS_ADDRESS_REG_OFFSET, 0x738);
  EXPECT_WRITE32(OTP_CTRL_DIRECT_ACCESS_CMD_REG_OFFSET,
                 {{OTP_CTRL_DIRECT_ACCESS_CMD_RD_BIT, true}});

  EXPECT_EQ(dif_otp_ctrl_dai_read_start(&otp_, kDifOtpCtrlPartitionSecret2,
                                        /*address=*/0x8),
            kDifOtpCtrlDaiOk);

  EXPECT_READ32(
      OTP_CTRL_DIRECT_ACCESS_REGWEN_REG_OFFSET,
      {{OTP_CTRL_DIRECT_ACCESS_REGWEN_DIRECT_ACCESS_REGWEN_BIT, true}});
  EXPECT_READ32(OTP_CTRL_DIRECT_ACCESS_RDATA_1_REG_OFFSET, 0x12345678);
  EXPECT_READ32(OTP_CTRL_DIRECT_ACCESS_RDATA_0_REG_OFFSET, 0x90abcdef);

  uint64_t val;
  EXPECT_EQ(dif_otp_ctrl_dai_read64_end(&otp_, &val), kDifOtpCtrlDaiOk);
  EXPECT_EQ(val, 0x1234567890abcdef);
}

TEST_F(DaiReadTest, Unaligned) {
  EXPECT_EQ(dif_otp_ctrl_dai_read_start(&otp_, kDifOtpCtrlPartitionHwCfg,
                                        /*address=*/0b01),
            kDifOtpCtrlDaiUnaligned);
  EXPECT_EQ(dif_otp_ctrl_dai_read_start(&otp_, kDifOtpCtrlPartitionSecret2,
                                        /*address=*/0b100),
            kDifOtpCtrlDaiUnaligned);
}

TEST_F(DaiReadTest, OutOfRange) {
  EXPECT_EQ(dif_otp_ctrl_dai_read_start(&otp_, kDifOtpCtrlPartitionHwCfg,
                                        /*address=*/0x100),
            kDifOtpCtrlDaiOutOfRange);
}

TEST_F(DaiReadTest, Busy) {
  EXPECT_READ32(
      OTP_CTRL_DIRECT_ACCESS_REGWEN_REG_OFFSET,
      {{OTP_CTRL_DIRECT_ACCESS_REGWEN_DIRECT_ACCESS_REGWEN_BIT, false}});
  EXPECT_EQ(dif_otp_ctrl_dai_read_start(&otp_, kDifOtpCtrlPartitionHwCfg,
                                        /*address=*/0x0),
            kDifOtpCtrlDaiBusy);

  EXPECT_READ32(
      OTP_CTRL_DIRECT_ACCESS_REGWEN_REG_OFFSET,
      {{OTP_CTRL_DIRECT_ACCESS_REGWEN_DIRECT_ACCESS_REGWEN_BIT, false}});
  uint32_t val32;
  EXPECT_EQ(dif_otp_ctrl_dai_read32_end(&otp_, &val32), kDifOtpCtrlDaiBusy);

  EXPECT_READ32(
      OTP_CTRL_DIRECT_ACCESS_REGWEN_REG_OFFSET,
      {{OTP_CTRL_DIRECT_ACCESS_REGWEN_DIRECT_ACCESS_REGWEN_BIT, false}});
  uint64_t val64;
  EXPECT_EQ(dif_otp_ctrl_dai_read64_end(&otp_, &val64), kDifOtpCtrlDaiBusy);
}

TEST_F(DaiReadTest, NullArgs) {
  EXPECT_EQ(dif_otp_ctrl_dai_read_start(nullptr, kDifOtpCtrlPartitionHwCfg,
                                        /*address=*/0x0),
            kDifOtpCtrlDaiBadArg);

  uint32_t val32;
  EXPECT_EQ(dif_otp_ctrl_dai_read32_end(nullptr, &val32), kDifOtpCtrlDaiBadArg);
  EXPECT_EQ(dif_otp_ctrl_dai_read32_end(&otp_, nullptr), kDifOtpCtrlDaiBadArg);

  uint64_t val64;
  EXPECT_EQ(dif_otp_ctrl_dai_read64_end(nullptr, &val64), kDifOtpCtrlDaiBadArg);
  EXPECT_EQ(dif_otp_ctrl_dai_read64_end(&otp_, nullptr), kDifOtpCtrlDaiBadArg);
}

class DaiProgramTest : public OtpTest {};

TEST_F(DaiProgramTest, Program32) {
  EXPECT_READ32(
      OTP_CTRL_DIRECT_ACCESS_REGWEN_REG_OFFSET,
      {{OTP_CTRL_DIRECT_ACCESS_REGWEN_DIRECT_ACCESS_REGWEN_BIT, true}});
  EXPECT_WRITE32(OTP_CTRL_DIRECT_ACCESS_ADDRESS_REG_OFFSET, 0x620);
  EXPECT_WRITE32(OTP_CTRL_DIRECT_ACCESS_WDATA_0_REG_OFFSET, 0x12345678);
  EXPECT_WRITE32(OTP_CTRL_DIRECT_ACCESS_CMD_REG_OFFSET,
                 {{OTP_CTRL_DIRECT_ACCESS_CMD_WR_BIT, true}});

  EXPECT_EQ(dif_otp_ctrl_dai_program32(&otp_, kDifOtpCtrlPartitionHwCfg,
                                       /*address=*/0x20, /*value=*/0x12345678),
            kDifOtpCtrlOk);
}

TEST_F(DaiProgramTest, Program64) {
  EXPECT_READ32(
      OTP_CTRL_DIRECT_ACCESS_REGWEN_REG_OFFSET,
      {{OTP_CTRL_DIRECT_ACCESS_REGWEN_DIRECT_ACCESS_REGWEN_BIT, true}});
  EXPECT_WRITE32(OTP_CTRL_DIRECT_ACCESS_ADDRESS_REG_OFFSET, 0x738);
  EXPECT_WRITE32(OTP_CTRL_DIRECT_ACCESS_WDATA_0_REG_OFFSET, 0x90abcdef);
  EXPECT_WRITE32(OTP_CTRL_DIRECT_ACCESS_WDATA_1_REG_OFFSET, 0x12345678);
  EXPECT_WRITE32(OTP_CTRL_DIRECT_ACCESS_CMD_REG_OFFSET,
                 {{OTP_CTRL_DIRECT_ACCESS_CMD_WR_BIT, true}});

  EXPECT_EQ(
      dif_otp_ctrl_dai_program64(&otp_, kDifOtpCtrlPartitionSecret2,
                                 /*address=*/0x8, /*value=*/0x1234567890abcdef),
      kDifOtpCtrlOk);
}

TEST_F(DaiProgramTest, BadPartition) {
  EXPECT_EQ(dif_otp_ctrl_dai_program32(&otp_, kDifOtpCtrlPartitionSecret1,
                                       /*address=*/0x0, /*value=*/42),
            kDifOtpCtrlDaiBadPartition);
  EXPECT_EQ(dif_otp_ctrl_dai_program64(&otp_, kDifOtpCtrlPartitionHwCfg,
                                       /*address=*/0x0, /*value=*/42),
            kDifOtpCtrlDaiBadPartition);

  // LC is never writeable.
  EXPECT_EQ(dif_otp_ctrl_dai_program32(&otp_, kDifOtpCtrlPartitionLifeCycle,
                                       /*address=*/0x0, /*value=*/42),
            kDifOtpCtrlDaiBadPartition);
}

TEST_F(DaiProgramTest, Unaligned) {
  EXPECT_EQ(dif_otp_ctrl_dai_program32(&otp_, kDifOtpCtrlPartitionHwCfg,
                                       /*address=*/0b01, /*value=*/42),
            kDifOtpCtrlDaiUnaligned);
  EXPECT_EQ(dif_otp_ctrl_dai_program64(&otp_, kDifOtpCtrlPartitionSecret2,
                                       /*address=*/0b100, /*value=*/42),
            kDifOtpCtrlDaiUnaligned);
}

TEST_F(DaiProgramTest, OutOfRange) {
  // Check that we can't write a digest directly.
  EXPECT_EQ(dif_otp_ctrl_dai_program32(&otp_, kDifOtpCtrlPartitionCreatorSwCfg,
                                       /*address=*/0x2f8, /*value=*/42),
            kDifOtpCtrlDaiOutOfRange);

  // Same digest check for 64-bit.
  EXPECT_EQ(dif_otp_ctrl_dai_program64(&otp_, kDifOtpCtrlPartitionSecret2,
                                       /*address=*/0x7a0, /*value=*/42),
            kDifOtpCtrlDaiOutOfRange);
}

TEST_F(DaiProgramTest, Busy) {
  EXPECT_READ32(
      OTP_CTRL_DIRECT_ACCESS_REGWEN_REG_OFFSET,
      {{OTP_CTRL_DIRECT_ACCESS_REGWEN_DIRECT_ACCESS_REGWEN_BIT, false}});
  EXPECT_EQ(dif_otp_ctrl_dai_program32(&otp_, kDifOtpCtrlPartitionHwCfg,
                                       /*address=*/0x0, /*value=*/42),
            kDifOtpCtrlDaiBusy);

  EXPECT_READ32(
      OTP_CTRL_DIRECT_ACCESS_REGWEN_REG_OFFSET,
      {{OTP_CTRL_DIRECT_ACCESS_REGWEN_DIRECT_ACCESS_REGWEN_BIT, false}});
  EXPECT_EQ(dif_otp_ctrl_dai_program64(&otp_, kDifOtpCtrlPartitionSecret0,
                                       /*address=*/0x0, /*value=*/42),
            kDifOtpCtrlDaiBusy);
}

TEST_F(DaiProgramTest, NullArgs) {
  EXPECT_EQ(dif_otp_ctrl_dai_program32(nullptr, kDifOtpCtrlPartitionHwCfg,
                                       /*address=*/0x0, /*value=*/42),
            kDifOtpCtrlDaiBadArg);
  EXPECT_EQ(dif_otp_ctrl_dai_program64(nullptr, kDifOtpCtrlPartitionSecret0,
                                       /*address=*/0x0, /*value=*/42),
            kDifOtpCtrlDaiBadArg);
}

class DaiDigestTest : public OtpTest {};

TEST_F(DaiDigestTest, DigestSw) {
  EXPECT_READ32(
      OTP_CTRL_DIRECT_ACCESS_REGWEN_REG_OFFSET,
      {{OTP_CTRL_DIRECT_ACCESS_REGWEN_DIRECT_ACCESS_REGWEN_BIT, true}});
  EXPECT_WRITE32(OTP_CTRL_DIRECT_ACCESS_ADDRESS_REG_OFFSET, 0x2f8);
  EXPECT_WRITE32(OTP_CTRL_DIRECT_ACCESS_WDATA_0_REG_OFFSET, 0x00abcdef);
  EXPECT_WRITE32(OTP_CTRL_DIRECT_ACCESS_WDATA_1_REG_OFFSET, 0xabcdef00);
  EXPECT_WRITE32(OTP_CTRL_DIRECT_ACCESS_CMD_REG_OFFSET,
                 {{OTP_CTRL_DIRECT_ACCESS_CMD_WR_BIT, true}});

  EXPECT_EQ(dif_otp_ctrl_dai_digest(&otp_, kDifOtpCtrlPartitionCreatorSwCfg,
                                    /*digest=*/0xabcdef0000abcdef),
            kDifOtpCtrlDaiOk);
}

TEST_F(DaiDigestTest, DigestHw) {
  EXPECT_READ32(
      OTP_CTRL_DIRECT_ACCESS_REGWEN_REG_OFFSET,
      {{OTP_CTRL_DIRECT_ACCESS_REGWEN_DIRECT_ACCESS_REGWEN_BIT, true}});
  EXPECT_WRITE32(OTP_CTRL_DIRECT_ACCESS_ADDRESS_REG_OFFSET, 0x600);
  EXPECT_WRITE32(OTP_CTRL_DIRECT_ACCESS_CMD_REG_OFFSET,
                 {{OTP_CTRL_DIRECT_ACCESS_CMD_DIGEST_BIT, true}});

  EXPECT_EQ(
      dif_otp_ctrl_dai_digest(&otp_, kDifOtpCtrlPartitionHwCfg, /*digest=*/0),
      kDifOtpCtrlDaiOk);
}

TEST_F(DaiDigestTest, BadPartition) {
  EXPECT_EQ(dif_otp_ctrl_dai_digest(&otp_, kDifOtpCtrlPartitionLifeCycle,
                                    /*digest=*/0),
            kDifOtpCtrlDaiBadPartition);
}

TEST_F(DaiDigestTest, Busy) {
  EXPECT_READ32(
      OTP_CTRL_DIRECT_ACCESS_REGWEN_REG_OFFSET,
      {{OTP_CTRL_DIRECT_ACCESS_REGWEN_DIRECT_ACCESS_REGWEN_BIT, false}});

  EXPECT_EQ(
      dif_otp_ctrl_dai_digest(&otp_, kDifOtpCtrlPartitionHwCfg, /*digest=*/0),
      kDifOtpCtrlDaiBusy);
}

TEST_F(DaiDigestTest, BadDigest) {
  EXPECT_EQ(dif_otp_ctrl_dai_digest(&otp_, kDifOtpCtrlPartitionHwCfg,
                                    /*digest=*/0xabcdef0000abcdef),
            kDifOtpCtrlDaiBadArg);
  EXPECT_EQ(dif_otp_ctrl_dai_digest(&otp_, kDifOtpCtrlPartitionCreatorSwCfg,
                                    /*digest=*/0),
            kDifOtpCtrlDaiBadArg);
}

TEST_F(DaiDigestTest, NullArgs) {
  EXPECT_EQ(dif_otp_ctrl_dai_digest(nullptr, kDifOtpCtrlPartitionCreatorSwCfg,
                                    /*digest=*/0xabcdef0000abcdef),
            kDifOtpCtrlDaiBadArg);
}

struct DigestParams {
  dif_otp_ctrl_partition_t partition;
  ptrdiff_t reg0, reg1;
};

class GetDigest : public OtpTest,
                  public testing::WithParamInterface<DigestParams> {};

TEST_P(GetDigest, GetDigest) {
  if (GetParam().partition == kDifOtpCtrlPartitionLifeCycle) {
    uint64_t digest;
    EXPECT_EQ(dif_otp_ctrl_get_digest(&otp_, GetParam().partition, &digest),
              kDifOtpCtrlDigestBadArg);
    return;
  }

  EXPECT_READ32(GetParam().reg1, 0xabcdef99);
  EXPECT_READ32(GetParam().reg0, 0x99abcdef);

  uint64_t digest;
  EXPECT_EQ(dif_otp_ctrl_get_digest(&otp_, GetParam().partition, &digest),
            kDifOtpCtrlDigestOk);
  EXPECT_EQ(digest, 0xabcdef9999abcdef);
}

TEST_P(GetDigest, BadDigest) {
  if (GetParam().partition == kDifOtpCtrlPartitionLifeCycle) {
    return;
  }

  EXPECT_READ32(GetParam().reg1, 0x0);
  EXPECT_READ32(GetParam().reg0, 0x0);

  uint64_t digest;
  EXPECT_EQ(dif_otp_ctrl_get_digest(&otp_, GetParam().partition, &digest),
            kDifOtpCtrlDigestMissing);
}

TEST_P(GetDigest, NullArgs) {
  uint64_t digest;
  EXPECT_EQ(dif_otp_ctrl_get_digest(nullptr, GetParam().partition, &digest),
            kDifOtpCtrlDigestBadArg);
  EXPECT_EQ(dif_otp_ctrl_get_digest(&otp_, GetParam().partition, nullptr),
            kDifOtpCtrlDigestBadArg);
}

INSTANTIATE_TEST_SUITE_P(AllDigests, GetDigest,
                         testing::Values(
                             DigestParams{
                                 kDifOtpCtrlPartitionCreatorSwCfg,
                                 OTP_CTRL_CREATOR_SW_CFG_DIGEST_0_REG_OFFSET,
                                 OTP_CTRL_CREATOR_SW_CFG_DIGEST_1_REG_OFFSET,
                             },
                             DigestParams{
                                 kDifOtpCtrlPartitionOwnerSwCfg,
                                 OTP_CTRL_OWNER_SW_CFG_DIGEST_0_REG_OFFSET,
                                 OTP_CTRL_OWNER_SW_CFG_DIGEST_1_REG_OFFSET,
                             },
                             DigestParams{
                                 kDifOtpCtrlPartitionHwCfg,
                                 OTP_CTRL_HW_CFG_DIGEST_0_REG_OFFSET,
                                 OTP_CTRL_HW_CFG_DIGEST_1_REG_OFFSET,
                             },
                             DigestParams{
                                 kDifOtpCtrlPartitionSecret0,
                                 OTP_CTRL_SECRET0_DIGEST_0_REG_OFFSET,
                                 OTP_CTRL_SECRET0_DIGEST_1_REG_OFFSET,
                             },
                             DigestParams{
                                 kDifOtpCtrlPartitionSecret1,
                                 OTP_CTRL_SECRET1_DIGEST_0_REG_OFFSET,
                                 OTP_CTRL_SECRET1_DIGEST_1_REG_OFFSET,
                             },
                             DigestParams{
                                 kDifOtpCtrlPartitionSecret2,
                                 OTP_CTRL_SECRET2_DIGEST_0_REG_OFFSET,
                                 OTP_CTRL_SECRET2_DIGEST_1_REG_OFFSET,
                             },
                             DigestParams{
                                 kDifOtpCtrlPartitionLifeCycle,
                                 0,
                                 0,
                             }));

class BlockingIoTest : public OtpTest {
 protected:
  static constexpr size_t kWords = 4;
};

TEST_F(BlockingIoTest, Read) {
  for (int i = 0; i < kWords; ++i) {
    auto offset = 0x300 + 0x10 + i * sizeof(uint32_t);
    EXPECT_READ32(OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET + offset, i + 1);
  }

  std::vector<uint32_t> buf(kWords);
  EXPECT_EQ(dif_otp_ctrl_read_blocking(&otp_, kDifOtpCtrlPartitionOwnerSwCfg,
                                       0x10, buf.data(), buf.size()),
            kDifOtpCtrlDaiOk);
  EXPECT_THAT(buf, ElementsAre(1, 2, 3, 4));
}

TEST_F(BlockingIoTest, BadPartition) {
  std::vector<uint32_t> buf(kWords);
  EXPECT_EQ(dif_otp_ctrl_read_blocking(&otp_, kDifOtpCtrlPartitionHwCfg, 0x10,
                                       buf.data(), buf.size()),
            kDifOtpCtrlDaiBadPartition);
}

TEST_F(BlockingIoTest, Unaligned) {
  std::vector<uint32_t> buf(kWords);
  EXPECT_EQ(dif_otp_ctrl_read_blocking(&otp_, kDifOtpCtrlPartitionOwnerSwCfg,
                                       0x11, buf.data(), buf.size()),
            kDifOtpCtrlDaiUnaligned);
}

TEST_F(BlockingIoTest, OutOfRange) {
  std::vector<uint32_t> buf(0x2f0);
  EXPECT_EQ(dif_otp_ctrl_read_blocking(&otp_, kDifOtpCtrlPartitionOwnerSwCfg,
                                       0x300, buf.data(), buf.size()),
            kDifOtpCtrlDaiOutOfRange);
  EXPECT_EQ(dif_otp_ctrl_read_blocking(&otp_, kDifOtpCtrlPartitionOwnerSwCfg,
                                       0x10, buf.data(), 0x2f0),
            kDifOtpCtrlDaiOutOfRange);
}

TEST_F(BlockingIoTest, NullArgs) {
  std::vector<uint32_t> buf(kWords);
  EXPECT_EQ(dif_otp_ctrl_read_blocking(nullptr, kDifOtpCtrlPartitionOwnerSwCfg,
                                       0x10, buf.data(), buf.size()),
            kDifOtpCtrlDaiBadArg);
  EXPECT_EQ(dif_otp_ctrl_read_blocking(&otp_, kDifOtpCtrlPartitionOwnerSwCfg,
                                       0x10, nullptr, buf.size()),
            kDifOtpCtrlDaiBadArg);
}

class TestIoTest : public OtpTest {
 protected:
  static constexpr size_t kWords = 4;
};

TEST_F(TestIoTest, Read) {
  for (int i = 0; i < kWords; ++i) {
    auto offset = 0x10 + i * sizeof(uint32_t);
    EXPECT_READ32(OTP_CTRL_TEST_ACCESS_REG_OFFSET + offset, i + 1);
  }

  std::vector<uint32_t> buf(kWords);
  EXPECT_EQ(dif_otp_ctrl_read_test(&otp_, 0x10, buf.data(), buf.size()),
            kDifOtpCtrlOk);
  EXPECT_THAT(buf, ElementsAre(1, 2, 3, 4));
}

TEST_F(TestIoTest, Write) {
  for (int i = 0; i < kWords; ++i) {
    auto offset = 0x10 + i * sizeof(uint32_t);
    EXPECT_WRITE32(OTP_CTRL_TEST_ACCESS_REG_OFFSET + offset, i + 1);
  }

  std::vector<uint32_t> buf = {1, 2, 3, 4};
  EXPECT_EQ(dif_otp_ctrl_write_test(&otp_, 0x10, buf.data(), buf.size()),
            kDifOtpCtrlOk);
}

TEST_F(TestIoTest, NullArgs) {
  std::vector<uint32_t> buf = {1, 2, 3, 4};
  EXPECT_EQ(dif_otp_ctrl_read_test(nullptr, 0x10, buf.data(), buf.size()),
            kDifOtpCtrlBadArg);
  EXPECT_EQ(dif_otp_ctrl_read_test(&otp_, 0x10, nullptr, buf.size()),
            kDifOtpCtrlBadArg);
  EXPECT_EQ(dif_otp_ctrl_write_test(nullptr, 0x10, buf.data(), buf.size()),
            kDifOtpCtrlBadArg);
  EXPECT_EQ(dif_otp_ctrl_write_test(&otp_, 0x10, nullptr, buf.size()),
            kDifOtpCtrlBadArg);
}

}  // namespace
}  // namespace dif_otp_ctrl_unittest
