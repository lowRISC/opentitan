// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/ip/soc_proxy/dif/autogen/dif_soc_proxy_autogen.h"

#include "gtest/gtest.h"
#include "sw/ip/base/dif/dif_test_base.h"
#include "sw/lib/sw/device/base/mmio.h"
#include "sw/lib/sw/device/base/mock_mmio.h"

#include "soc_proxy_regs.h"  // Generated.

namespace dif_soc_proxy_autogen_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Eq;
using ::testing::Test;

class SocProxyTest : public Test, public MmioTest {
 protected:
  dif_soc_proxy_t soc_proxy_ = {.base_addr = dev().region()};
};

class InitTest : public SocProxyTest {};

TEST_F(InitTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_soc_proxy_init(dev().region(), nullptr));
}

TEST_F(InitTest, Success) {
  EXPECT_DIF_OK(dif_soc_proxy_init(dev().region(), &soc_proxy_));
}

class AlertForceTest : public SocProxyTest {};

TEST_F(AlertForceTest, NullArgs) {
  EXPECT_DIF_BADARG(
      dif_soc_proxy_alert_force(nullptr, kDifSocProxyAlertFatalAlertIntg));
}

TEST_F(AlertForceTest, BadAlert) {
  EXPECT_DIF_BADARG(dif_soc_proxy_alert_force(
      nullptr, static_cast<dif_soc_proxy_alert_t>(32)));
}

TEST_F(AlertForceTest, Success) {
  // Force first alert.
  EXPECT_WRITE32(SOC_PROXY_ALERT_TEST_REG_OFFSET,
                 {{SOC_PROXY_ALERT_TEST_FATAL_ALERT_INTG_BIT, true}});
  EXPECT_DIF_OK(
      dif_soc_proxy_alert_force(&soc_proxy_, kDifSocProxyAlertFatalAlertIntg));
}

}  // namespace
}  // namespace dif_soc_proxy_autogen_unittest
