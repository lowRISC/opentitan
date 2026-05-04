// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_rom_ctrl.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

extern "C" {
#include "hw/top/rom_ctrl_regs.h"  // Generated.
}  // extern "C"

namespace dif_rom_ctrl_test {
namespace {
using mock_mmio::MmioTest;
using mock_mmio::MockDevice;
using testing::Test;

class RomCtrlTest : public Test, public MmioTest {
 protected:
  dif_rom_ctrl_t rom_ctrl_;

  void SetUp() override {
    EXPECT_DIF_OK(dif_rom_ctrl_init(dev().region(), &rom_ctrl_));
  }
};

class RomCtrlInitTest : public RomCtrlTest {};

TEST_F(RomCtrlInitTest, BadArgs) {
  EXPECT_DIF_BADARG(dif_rom_ctrl_init(dev().region(), nullptr));
}

class FatalAlertCauseTest : public RomCtrlTest {};

TEST_F(FatalAlertCauseTest, NullArgs) {
  dif_rom_ctrl_fatal_alert_causes_t causes;
  EXPECT_DIF_BADARG(dif_rom_ctrl_get_fatal_alert_cause(nullptr, &causes));
  EXPECT_DIF_BADARG(dif_rom_ctrl_get_fatal_alert_cause(&rom_ctrl_, nullptr));
}

TEST_F(FatalAlertCauseTest, SuccessNoError) {
  EXPECT_READ32(ROM_CTRL_FATAL_ALERT_CAUSE_REG_OFFSET, 0);

  dif_rom_ctrl_fatal_alert_causes_t causes = 0xFFFFFFFF;
  EXPECT_DIF_OK(dif_rom_ctrl_get_fatal_alert_cause(&rom_ctrl_, &causes));
  EXPECT_EQ(causes, 0);
}

TEST_F(FatalAlertCauseTest, SuccessCheckerError) {
  EXPECT_READ32(ROM_CTRL_FATAL_ALERT_CAUSE_REG_OFFSET,
                1 << kDifRomCtrlFatalAlertCauseCheckerError);

  dif_rom_ctrl_fatal_alert_causes_t causes = 0;
  EXPECT_DIF_OK(dif_rom_ctrl_get_fatal_alert_cause(&rom_ctrl_, &causes));
  EXPECT_EQ(causes, 1 << kDifRomCtrlFatalAlertCauseCheckerError);
}

TEST_F(FatalAlertCauseTest, SuccessIntegrityError) {
  EXPECT_READ32(ROM_CTRL_FATAL_ALERT_CAUSE_REG_OFFSET,
                1 << kDifRomCtrlFatalAlertCauseIntegrityError);

  dif_rom_ctrl_fatal_alert_causes_t causes = 0;
  EXPECT_DIF_OK(dif_rom_ctrl_get_fatal_alert_cause(&rom_ctrl_, &causes));
  EXPECT_EQ(causes, 1 << kDifRomCtrlFatalAlertCauseIntegrityError);
}

class DigestTest : public RomCtrlTest {};

TEST_F(DigestTest, NullArgs) {
  dif_rom_ctrl_digest_t digest;
  EXPECT_DIF_BADARG(dif_rom_ctrl_get_digest(nullptr, &digest));
  EXPECT_DIF_BADARG(dif_rom_ctrl_get_digest(&rom_ctrl_, nullptr));
}

TEST_F(DigestTest, Success) {
  for (int i = 0; i < ROM_CTRL_DIGEST_MULTIREG_COUNT; ++i) {
    EXPECT_READ32(ROM_CTRL_DIGEST_0_REG_OFFSET + i * 4, i);
  }

  dif_rom_ctrl_digest_t digest;
  EXPECT_DIF_OK(dif_rom_ctrl_get_digest(&rom_ctrl_, &digest));
  for (int i = 0; i < ROM_CTRL_DIGEST_MULTIREG_COUNT; ++i) {
    EXPECT_EQ(digest.digest[i], i);
  }
}

class ExpectedDigestTest : public RomCtrlTest {};

TEST_F(ExpectedDigestTest, NullArgs) {
  dif_rom_ctrl_digest_t digest;
  EXPECT_DIF_BADARG(dif_rom_ctrl_get_expected_digest(nullptr, &digest));
  EXPECT_DIF_BADARG(dif_rom_ctrl_get_expected_digest(&rom_ctrl_, nullptr));
}

TEST_F(ExpectedDigestTest, Success) {
  for (int i = 0; i < ROM_CTRL_EXP_DIGEST_MULTIREG_COUNT; ++i) {
    EXPECT_READ32(ROM_CTRL_EXP_DIGEST_0_REG_OFFSET + i * 4, i);
  }

  dif_rom_ctrl_digest_t digest;
  EXPECT_DIF_OK(dif_rom_ctrl_get_expected_digest(&rom_ctrl_, &digest));
  for (int i = 0; i < ROM_CTRL_EXP_DIGEST_MULTIREG_COUNT; ++i) {
    EXPECT_EQ(digest.digest[i], i);
  }
}

}  // namespace
}  // namespace dif_rom_ctrl_test
