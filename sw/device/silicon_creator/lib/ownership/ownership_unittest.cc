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
#include "sw/device/silicon_creator/lib/drivers/mock_flash_ctrl.h"
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
using ::rom_test::FlashCfg;
using ::rom_test::FlashPerms;
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
  rom_test::NiceMockFlashCtrl flash_ctrl_;
  rom_test::MockLifecycle lifecycle_;
  rom_test::MockOwnershipKey ownership_key_;
  rom_test::MockBootData mock_bootdata_;
};

TEST_F(OwnershipInitTest, InitWithRecoveryState) {
  boot_data_t bootdata = {.ownership_state = kOwnershipStateRecovery};
  owner_config_t config = {};
  owner_application_keyring_t keyring = {};

  EXPECT_CALL(flash_ctrl_, InfoRead(&kFlashCtrlInfoPageOwnerSlot0, _, _, _))
      .WillOnce(Return(kErrorOk));
  EXPECT_CALL(lifecycle_, DeviceId(_))
      .WillOnce(SetArgPointee<0>((lifecycle_device_id_t){0}));
  EXPECT_CALL(ownership_key_, seal_check(0))
      .WillOnce(Return(kErrorOwnershipInvalidInfoPage));
  EXPECT_CALL(ownership_key_, validate(_, _, _, _, _, _, _))
      .WillOnce(Return(kErrorOwnershipInvalidInfoPage));

  EXPECT_CALL(flash_ctrl_, InfoRead(&kFlashCtrlInfoPageOwnerSlot1, _, _, _))
      .WillOnce(Return(kErrorOk));
  EXPECT_CALL(lifecycle_, DeviceId(_))
      .WillOnce(SetArgPointee<0>((lifecycle_device_id_t){0}));
  EXPECT_CALL(ownership_key_, seal_check(1))
      .WillOnce(Return(kErrorOwnershipInvalidInfoPage));
  EXPECT_CALL(ownership_key_, validate(_, _, _, _, _, _, _))
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

  EXPECT_CALL(flash_ctrl_, InfoRead(&kFlashCtrlInfoPageOwnerSlot0, _, _, _))
      .WillOnce(Return(kErrorOk));
  EXPECT_CALL(lifecycle_, DeviceId(_))
      .WillOnce(SetArgPointee<0>((lifecycle_device_id_t){0}));
  EXPECT_CALL(ownership_key_, seal_check(0))
      .WillOnce(Return(kErrorOwnershipInvalidInfoPage));
  EXPECT_CALL(ownership_key_, validate(_, _, _, _, _, _, _))
      .WillOnce(Return(kErrorOwnershipInvalidInfoPage));

  EXPECT_CALL(flash_ctrl_, InfoRead(&kFlashCtrlInfoPageOwnerSlot1, _, _, _))
      .WillOnce(Return(kErrorOk));
  EXPECT_CALL(lifecycle_, DeviceId(_))
      .WillOnce(SetArgPointee<0>((lifecycle_device_id_t){0}));
  EXPECT_CALL(ownership_key_, seal_check(1))
      .WillOnce(Return(kErrorOwnershipInvalidInfoPage));
  EXPECT_CALL(ownership_key_, validate(_, _, _, _, _, _, _))
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
