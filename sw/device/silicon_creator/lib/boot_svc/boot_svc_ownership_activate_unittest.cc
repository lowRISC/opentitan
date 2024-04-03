// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_ownership_activate.h"

#include <string.h>

#include "gtest/gtest.h"
#include "sw/device/silicon_creator/lib/boot_svc/mock_boot_svc_header.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace boot_svc_ownership_activate_unittest {
namespace {
using ::testing::ElementsAreArray;

class BootSvcOwnershipActivateTest : public rom_test::RomTest {
 protected:
  rom_test::MockBootSvcHeader boot_svc_header_;
};

TEST_F(BootSvcOwnershipActivateTest, ReqInit) {
  boot_svc_ownership_activate_req_t msg{};
  constexpr uint32_t primary_bl0_slot = 0;
  constexpr uint32_t erase_previous = 1;
  constexpr nonce_t nonce = {0x55555555, 0xAAAAAAAA};
  constexpr owner_signature_t signature = {{100, 101, 102, 103, 104, 105, 106,
                                            107, 108, 109, 110, 111, 112, 113,
                                            114, 115}};
  EXPECT_CALL(boot_svc_header_, Finalize(kBootSvcOwnershipActivateReqType,
                                         sizeof(msg), &msg.header));

  boot_svc_ownership_activate_req_init(primary_bl0_slot, erase_previous, nonce,
                                       &signature, &msg);

  EXPECT_EQ(msg.primary_bl0_slot, primary_bl0_slot);
  EXPECT_EQ(msg.erase_previous, erase_previous);
  EXPECT_EQ(msg.nonce.value[0], nonce.value[0]);
  EXPECT_EQ(msg.nonce.value[1], nonce.value[1]);
  EXPECT_EQ(memcmp(&msg.signature, &signature, sizeof(signature)), 0);
}

TEST_F(BootSvcOwnershipActivateTest, ResInit) {
  boot_svc_ownership_activate_res_t msg{};
  constexpr rom_error_t kStatus = kErrorOk;
  EXPECT_CALL(boot_svc_header_, Finalize(kBootSvcOwnershipActivateResType,
                                         sizeof(msg), &msg.header));

  boot_svc_ownership_activate_res_init(kStatus, &msg);

  EXPECT_EQ(msg.status, kStatus);
}

}  // namespace
}  // namespace boot_svc_ownership_activate_unittest
