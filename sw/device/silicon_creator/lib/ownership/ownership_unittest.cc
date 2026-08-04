// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/ownership/ownership.h"

#include <stdint.h>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "sw/device/lib/base/global_mock.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/mock_abs_mmio.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/boot_svc/mock_boot_svc_header.h"
#ifdef HAS_RRAM_CTRL
#include "sw/device/silicon_creator/lib/drivers/mock_rram_ctrl.h"
#else
#include "sw/device/silicon_creator/lib/drivers/mock_flash_ctrl.h"
#endif  // HAS_RRAM_CTRL
#include "sw/device/silicon_creator/lib/drivers/mock_hmac.h"
#include "sw/device/silicon_creator/lib/drivers/mock_lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/mock_rnd.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/mock_boot_data.h"
#include "sw/device/silicon_creator/lib/nonce.h"
#include "sw/device/silicon_creator/lib/ownership/datatypes.h"
#include "sw/device/silicon_creator/lib/ownership/mock_ownership_key.h"
#include "sw/device/silicon_creator/lib/ownership/owner_block.h"
#include "sw/device/silicon_creator/lib/ownership/ownership_activate.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace {
using ::testing::_;
using ::testing::Return;
using ::testing::SetArgPointee;

// We don't use a mock here since it'd be overkill; expectations are easier
// to write on a global string, instead. This also produces a simpler error
// message instead of a tower of failed expectations.
static std::string *uart_buf = new std::string;
extern "C" void uart_putchar(uint8_t c) { uart_buf->push_back(c); }

class OwnershipInitTest : public rom_test::RomTest {
 protected:
  rom_test::MockHmac hmac_;
  rom_test::MockRnd rnd_;
#ifdef HAS_RRAM_CTRL
  rom_test::NiceMockRramCtrl rram_ctrl_;
#else
  rom_test::NiceMockFlashCtrl flash_ctrl_;
#endif  // HAS_RRAM_CTRL
  rom_test::MockLifecycle lifecycle_;
  rom_test::MockOwnershipKey ownership_key_;
  rom_test::MockBootData mock_bootdata_;

  /**
   * Sets an expectation that owner slot 0 (or 1, if `slot1` is true) is read.
   *
   * OwnerSlot0/1 are emulated info pages on RRAM: `nvm_ctrl_info_read()`
   * becomes a plain data-partition `DataRead` at the page's base address
   * (`ownership.c` always reads at offset 0) rather than an `InfoRead`.
   */
  void ExpectOwnerSlotRead(bool slot1) {
#ifdef HAS_RRAM_CTRL
    const rram_ctrl_info_page_t &page =
        slot1 ? kRramCtrlInfoPageOwnerSlot1 : kRramCtrlInfoPageOwnerSlot0;
    EXPECT_CALL(rram_ctrl_,
                DataRead(page.page_id * RRAM_CTRL_PARAM_BYTES_PER_PAGE, _, _))
        .WillOnce(Return(kErrorOk));
#else
    const flash_ctrl_info_page_t &page =
        slot1 ? kFlashCtrlInfoPageOwnerSlot1 : kFlashCtrlInfoPageOwnerSlot0;
    EXPECT_CALL(flash_ctrl_, InfoRead(&page, _, _, _))
        .WillOnce(Return(kErrorOk));
#endif  // HAS_RRAM_CTRL
  }
};

TEST_F(OwnershipInitTest, InitWithRecoveryState) {
  boot_data_t bootdata = {.ownership_state = kOwnershipStateRecovery};
  owner_config_t config = {};
  owner_application_keyring_t keyring = {};

  ExpectOwnerSlotRead(/*slot1=*/false);
  EXPECT_CALL(lifecycle_, DeviceId(_))
      .WillOnce(SetArgPointee<0>((lifecycle_device_id_t){0}));
  EXPECT_CALL(ownership_key_, seal_check(0))
      .WillOnce(Return(kErrorOwnershipInvalidInfoPage));
  EXPECT_CALL(ownership_key_, validate(_, _, _, _, _, _, _, _))
      .WillOnce(Return(kErrorOwnershipInvalidInfoPage));

  ExpectOwnerSlotRead(/*slot1=*/true);
  EXPECT_CALL(lifecycle_, DeviceId(_))
      .WillOnce(SetArgPointee<0>((lifecycle_device_id_t){0}));
  EXPECT_CALL(ownership_key_, seal_check(1))
      .WillOnce(Return(kErrorOwnershipInvalidInfoPage));
  EXPECT_CALL(ownership_key_, validate(_, _, _, _, _, _, _, _))
      .WillOnce(Return(kErrorOwnershipInvalidInfoPage));

  EXPECT_CALL(rnd_, Uint32()).WillRepeatedly(Return(0));
  EXPECT_EQ(ownership_init(&bootdata, &config, &keyring),
            kErrorOwnershipNoOwner);
}

class OwnershipInitInvalidPagesTest
    : public OwnershipInitTest,
      public testing::WithParamInterface<ownership_state_t> {};

TEST_P(OwnershipInitInvalidPagesTest, InitWithInfoPageCorrupted) {
  boot_data_t bootdata = {.ownership_state = GetParam()};
  owner_config_t config = {};
  owner_application_keyring_t keyring = {};

  ExpectOwnerSlotRead(/*slot1=*/false);
  EXPECT_CALL(lifecycle_, DeviceId(_))
      .WillOnce(SetArgPointee<0>((lifecycle_device_id_t){0}));
  EXPECT_CALL(ownership_key_, seal_check(0))
      .WillOnce(Return(kErrorOwnershipInvalidInfoPage));
  EXPECT_CALL(ownership_key_, validate(_, _, _, _, _, _, _, _))
      .WillOnce(Return(kErrorOwnershipInvalidInfoPage));

  ExpectOwnerSlotRead(/*slot1=*/true);
  EXPECT_CALL(lifecycle_, DeviceId(_))
      .WillOnce(SetArgPointee<0>((lifecycle_device_id_t){0}));
  EXPECT_CALL(ownership_key_, seal_check(1))
      .WillOnce(Return(kErrorOwnershipInvalidInfoPage));
  EXPECT_CALL(ownership_key_, validate(_, _, _, _, _, _, _, _))
      .WillOnce(Return(kErrorOwnershipInvalidInfoPage));

  EXPECT_CALL(rnd_, Uint32()).WillRepeatedly(Return(0));
  EXPECT_CALL(mock_bootdata_, Write(_)).WillOnce(Return(kErrorOk));

  EXPECT_EQ(ownership_init(&bootdata, &config, &keyring),
            kErrorOwnershipBadInfoPage);
}

INSTANTIATE_TEST_SUITE_P(AllCases, OwnershipInitInvalidPagesTest,
                         testing::Values(kOwnershipStateLockedOwner,
                                         kOwnershipStateUnlockedSelf));
}  // namespace
