// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_ownership_history.h"

#include <string.h>

#include "gtest/gtest.h"
#include "sw/device/silicon_creator/lib/boot_svc/mock_boot_svc_header.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace boot_svc_ownership_history_unittest {
namespace {
using ::testing::ElementsAreArray;

class BootSvcOwnershipHistoryTest : public rom_test::RomTest {
 protected:
  rom_test::MockBootSvcHeader boot_svc_header_;
};

TEST_F(BootSvcOwnershipHistoryTest, ReqInit) {
  boot_svc_ownership_history_req_t msg{};
  EXPECT_CALL(boot_svc_header_, Finalize(kBootSvcOwnershipHistoryReqType,
                                         sizeof(msg), &msg.header));

  boot_svc_ownership_history_req_init(&msg);
}

TEST_F(BootSvcOwnershipHistoryTest, ResInit) {
  boot_svc_ownership_history_res_t msg{};
  constexpr rom_error_t kStatus = kErrorOk;
  const uint32_t history_digest[8] = {1, 2, 3, 4, 5, 6, 7, 8};
  EXPECT_CALL(boot_svc_header_, Finalize(kBootSvcOwnershipHistoryResType,
                                         sizeof(msg), &msg.header));

  boot_svc_ownership_history_res_init(kStatus, history_digest, &msg);

  EXPECT_EQ(msg.status, kStatus);
  EXPECT_EQ(
      memcmp(&msg.history_digest, &history_digest, sizeof(history_digest)), 0);
}

}  // namespace
}  // namespace boot_svc_ownership_history_unittest
