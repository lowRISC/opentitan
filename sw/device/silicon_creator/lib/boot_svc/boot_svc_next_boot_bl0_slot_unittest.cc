// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_next_boot_bl0_slot.h"

#include "gtest/gtest.h"
#include "sw/device/silicon_creator/lib/boot_svc/mock_boot_svc_header.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace boot_svc_next_boot_bl0_slot_unittest {
namespace {

class BootSvcNextBootBl0SlotTest : public rom_test::RomTest {
 protected:
  rom_test::MockBootSvcHeader boot_svc_header_;
};

TEST_F(BootSvcNextBootBl0SlotTest, ReqInit) {
  boot_svc_next_boot_bl0_slot_req_t msg{};
  constexpr uint32_t kNextSlot = kBootSvcNextBootBl0SlotB;
  EXPECT_CALL(boot_svc_header_,
              Finalize(kBootSvcNextBl0SlotReqType, sizeof(msg), &msg.header));

  boot_svc_next_boot_bl0_slot_req_init(kNextSlot, &msg);

  EXPECT_EQ(msg.next_bl0_slot, kNextSlot);
}

TEST_F(BootSvcNextBootBl0SlotTest, ResInit) {
  boot_svc_next_boot_bl0_slot_res_t msg{};
  constexpr rom_error_t kStatus = kErrorOk;
  EXPECT_CALL(boot_svc_header_,
              Finalize(kBootSvcNextBl0SlotResType, sizeof(msg), &msg.header));

  boot_svc_next_boot_bl0_slot_res_init(kStatus, &msg);

  EXPECT_EQ(msg.status, kStatus);
}

}  // namespace
}  // namespace boot_svc_next_boot_bl0_slot_unittest
