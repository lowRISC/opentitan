// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This file is auto-generated.

#include "sw/device/lib/dif/autogen/dif_aes_autogen.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"

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
  EXPECT_EQ(dif_aes_init({.base_addr = dev().region()}, nullptr), kDifBadArg);
}

TEST_F(InitTest, Success) {
  EXPECT_EQ(dif_aes_init({.base_addr = dev().region()}, &aes_), kDifOk);
}

class AlertForceTest : public AesTest {};

TEST_F(AlertForceTest, NullArgs) {
  EXPECT_EQ(dif_aes_alert_force(nullptr, kDifAesAlertRecovCtrlUpdateErr),
            kDifBadArg);
}

TEST_F(AlertForceTest, BadAlert) {
  EXPECT_EQ(dif_aes_alert_force(nullptr, static_cast<dif_aes_alert_t>(32)),
            kDifBadArg);
}

TEST_F(AlertForceTest, Success) {
  // Force first alert.
  EXPECT_WRITE32(AES_ALERT_TEST_REG_OFFSET,
                 {{AES_ALERT_TEST_RECOV_CTRL_UPDATE_ERR_BIT, true}});
  EXPECT_EQ(dif_aes_alert_force(&aes_, kDifAesAlertRecovCtrlUpdateErr), kDifOk);

  // Force last alert.
  EXPECT_WRITE32(AES_ALERT_TEST_REG_OFFSET,
                 {{AES_ALERT_TEST_FATAL_FAULT_BIT, true}});
  EXPECT_EQ(dif_aes_alert_force(&aes_, kDifAesAlertFatalFault), kDifOk);
}

}  // namespace
}  // namespace dif_aes_autogen_unittest
