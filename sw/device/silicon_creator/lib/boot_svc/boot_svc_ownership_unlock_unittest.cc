// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_ownership_unlock.h"

#include <string.h>

#include "gtest/gtest.h"
#include "sw/device/silicon_creator/lib/boot_svc/mock_boot_svc_header.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace boot_svc_ownership_unlock_unittest {
namespace {
using ::testing::ElementsAreArray;

class BootSvcOwnershipUnlockTest : public rom_test::RomTest {
 protected:
  rom_test::MockBootSvcHeader boot_svc_header_;
};

TEST_F(BootSvcOwnershipUnlockTest, ReqInit) {
  boot_svc_ownership_unlock_req_t msg{};
  constexpr uint32_t unlock_mode = kBootSvcUnlockAny;
  constexpr nonce_t nonce = {0x55555555, 0xAAAAAAAA};
  constexpr owner_key_t next_owner_key = {
      {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15}};
  constexpr owner_signature_t signature = {{100, 101, 102, 103, 104, 105, 106,
                                            107, 108, 109, 110, 111, 112, 113,
                                            114, 115}};
  EXPECT_CALL(boot_svc_header_, Finalize(kBootSvcOwnershipUnlockReqType,
                                         sizeof(msg), &msg.header));

  boot_svc_ownership_unlock_req_init(unlock_mode, nonce, &next_owner_key,
                                     &signature, &msg);

  EXPECT_EQ(msg.unlock_mode, unlock_mode);
  EXPECT_EQ(msg.nonce.value[0], nonce.value[0]);
  EXPECT_EQ(msg.nonce.value[1], nonce.value[1]);
  EXPECT_EQ(
      memcmp(&msg.next_owner_key, &next_owner_key, sizeof(next_owner_key)), 0);
  EXPECT_EQ(memcmp(&msg.signature, &signature, sizeof(signature)), 0);
}

TEST_F(BootSvcOwnershipUnlockTest, ResInit) {
  boot_svc_ownership_unlock_res_t msg{};
  constexpr rom_error_t kStatus = kErrorOk;
  EXPECT_CALL(boot_svc_header_, Finalize(kBootSvcOwnershipUnlockResType,
                                         sizeof(msg), &msg.header));

  boot_svc_ownership_unlock_res_init(kStatus, &msg);

  EXPECT_EQ(msg.status, kStatus);
}

}  // namespace
}  // namespace boot_svc_ownership_unlock_unittest
