// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_min_bl0_sec_ver.h"

#include "gtest/gtest.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/boot_svc/mock_boot_svc_header.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace boot_svc_min_bl0_sec_ver_unittest {
namespace {

class BootSvcMinBl0SecVerTest : public rom_test::RomTest {
 protected:
  rom_test::MockBootSvcHeader boot_svc_header_;
};

TEST_F(BootSvcMinBl0SecVerTest, ReqInit) {
  boot_svc_min_bl0_sec_ver_req_t msg{};
  constexpr uint32_t kMinBl0SecVersion = 0x12345678;
  EXPECT_CALL(boot_svc_header_,
              Finalize(kBootSvcMinBl0SecVerReqType, sizeof(msg), &msg.header));

  boot_svc_min_bl0_sec_ver_req_init(kMinBl0SecVersion, &msg);

  EXPECT_EQ(msg.min_bl0_sec_ver, kMinBl0SecVersion);
}

TEST_F(BootSvcMinBl0SecVerTest, ResInit) {
  boot_svc_min_bl0_sec_ver_res_t msg{};
  constexpr rom_error_t kStatus = kErrorOk;
  EXPECT_CALL(boot_svc_header_,
              Finalize(kBootSvcMinBl0SecVerResType, sizeof(msg), &msg.header));

  boot_svc_min_bl0_sec_ver_res_init(kStatus, &msg);

  EXPECT_EQ(msg.status, kStatus);
}

}  // namespace
}  // namespace boot_svc_min_bl0_sec_ver_unittest
