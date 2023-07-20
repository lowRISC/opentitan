// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/device/lib/dif/autogen/dif_aes_autogen.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "aes_regs.h"  // Generated.

namespace dif_aes_autogen_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Eq;
using ::testing::Test;

class AesTest : public Test, public MmioTest {
 protected:
  dif_aes_t aes_ = {.base_addr = dev().region()};
};

class InitTest : public AesTest {};

TEST_F(InitTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_aes_init(dev().region(), nullptr));
}

TEST_F(InitTest, Success) {
  EXPECT_DIF_OK(dif_aes_init(dev().region(), &aes_));
}

class AlertForceTest : public AesTest {};

TEST_F(AlertForceTest, NullArgs) {
  EXPECT_DIF_BADARG(
      dif_aes_alert_force(nullptr, kDifAesAlertRecovCtrlUpdateErr));
}

TEST_F(AlertForceTest, BadAlert) {
  EXPECT_DIF_BADARG(
      dif_aes_alert_force(nullptr, static_cast<dif_aes_alert_t>(32)));
}

TEST_F(AlertForceTest, Success) {
  // Force first alert.
  EXPECT_WRITE32(AES_ALERT_TEST_REG_OFFSET,
                 {{AES_ALERT_TEST_RECOV_CTRL_UPDATE_ERR_BIT, true}});
  EXPECT_DIF_OK(dif_aes_alert_force(&aes_, kDifAesAlertRecovCtrlUpdateErr));

  // Force last alert.
  EXPECT_WRITE32(AES_ALERT_TEST_REG_OFFSET,
                 {{AES_ALERT_TEST_FATAL_FAULT_BIT, true}});
  EXPECT_DIF_OK(dif_aes_alert_force(&aes_, kDifAesAlertFatalFault));
}

}  // namespace
}  // namespace dif_aes_autogen_unittest
