// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_enter_rescue.h"

#include <string.h>

#include "gtest/gtest.h"
#include "sw/device/silicon_creator/lib/boot_svc/mock_boot_svc_header.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace boot_svc_enter_rescue_unittest {
namespace {
using ::testing::ElementsAreArray;

class BootSvcEnterRescueTest : public rom_test::RomTest {
 protected:
  rom_test::MockBootSvcHeader boot_svc_header_;
};

TEST_F(BootSvcEnterRescueTest, ReqInit) {
  boot_svc_enter_rescue_req_t msg{};
  EXPECT_CALL(boot_svc_header_,
              Finalize(kBootSvcEnterRescueReqType, sizeof(msg), &msg.header));

  boot_svc_enter_rescue_req_init(&msg);
}

TEST_F(BootSvcEnterRescueTest, ResInit) {
  boot_svc_enter_rescue_res_t msg{};
  constexpr rom_error_t kStatus = kErrorOk;
  EXPECT_CALL(boot_svc_header_,
              Finalize(kBootSvcEnterRescueResType, sizeof(msg), &msg.header));

  boot_svc_enter_rescue_res_init(kStatus, &msg);

  EXPECT_EQ(msg.status, kStatus);
}

}  // namespace
}  // namespace boot_svc_enter_rescue_unittest
