// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdio.h>
#include <tuple>

#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/boot_log.h"
#include "sw/device/silicon_creator/lib/drivers/mock_flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/mock_lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/mock_retention_sram.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/rescue/mock_xmodem.h"
#include "sw/device/silicon_creator/lib/rescue/rescue.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

// #include "testing/base/public/gmock.h"
// #include "testing/base/public/gunit.h"

namespace rescue_xmodem_unittest {
namespace {
using ::testing::_;
using ::testing::Return;

using rom_test::FlashPerms;
extern "C" {
rom_error_t protocol_inner(rescue_state_t *state);
}

class XmodemTest : public rom_test::RomTest {
 protected:
  void SetUp() override {
    rescue_state_init(
        &state_, &boot_data_, &boot_log_,
        reinterpret_cast<const owner_rescue_config_t *>(kHardenedBoolFalse));
  }

  void HandleFrame(size_t frame_size) {
    ON_CALL(xmodem_, RecvFrame(_, _, _, _, _, _))
        .WillByDefault([frame_size](auto, uint32_t, uint8_t *data,
                                    size_t len_avail, size_t *rxlen, auto) {
          *rxlen = frame_size;
          return kErrorOk;
        });

    ON_CALL(xmodem_, Ack(_, _)).WillByDefault(Return());
  }

  void HandleFlashWrite() {
    ON_CALL(flash_, DataDefaultPermsSet(_)).WillByDefault(Return());
    ON_CALL(flash_, DataErase(_, _)).WillByDefault(Return(kErrorOk));
    ON_CALL(flash_, DataWrite(_, _, _)).WillByDefault(Return(kErrorOk));
  }

  void HandleOwnerWrite() {
    ON_CALL(flash_, InfoErase(_, _)).WillByDefault(Return(kErrorOk));
    ON_CALL(flash_, InfoWrite(_, _, _, _)).WillByDefault(Return(kErrorOk));
  }

  void HandleOwnerRead() {
    ON_CALL(flash_, InfoRead(_, _, _, _)).WillByDefault(Return(kErrorOk));
  }

  void HandleRetentionRam() {
    ON_CALL(retention_sram_, Get()).WillByDefault(Return(&retram_));
  }

  void HandleDeviceId() {
    ON_CALL(lifecycle_, DeviceId(_)).WillByDefault(Return());
  }

  rescue_state_t state_;
  boot_data_t boot_data_;
  boot_log_t boot_log_;
  retention_sram_t retram_;

  rom_test::NiceMockXmodem xmodem_;
  rom_test::NiceMockFlashCtrl flash_;
  rom_test::NiceMockRetentionSram retention_sram_;
  rom_test::NiceMockLifecycle lifecycle_;
};

class XmodemRecvTests : public XmodemTest,
                        public testing::WithParamInterface<
                            std::tuple<rescue_mode_t, size_t, size_t>> {};

// Tests that the upload path never overflows the data buffer
// and that the offset is reset to zero after processing.
TEST_P(XmodemRecvTests, UploadBlocks) {
  rescue_mode_t mode;
  size_t blksz, nblocks;
  std::tie(mode, blksz, nblocks) = GetParam();

  rescue_validate_mode(mode, &state_);
  HandleFrame(blksz);
  HandleFlashWrite();
  HandleOwnerWrite();
  HandleRetentionRam();

  for (size_t i = 0; i < nblocks; ++i) {
    EXPECT_EQ(protocol_inner(&state_), kErrorOk);
    EXPECT_LT(state_.offset, 2048);
  }

  // At the end, we expect the offset to be reset to zero.
  EXPECT_EQ(state_.offset, 0);
}

// Tests that the upload path never overflows the data buffer
// and that the offset is reset to zero after processing a short buffer.
TEST_P(XmodemRecvTests, UploadShort) {
  rescue_mode_t mode;
  size_t blksz, nblocks;
  std::tie(mode, blksz, nblocks) = GetParam();
  nblocks -= 1;

  rescue_validate_mode(mode, &state_);
  HandleFrame(blksz);
  HandleFlashWrite();
  HandleOwnerWrite();
  HandleRetentionRam();

  for (size_t i = 0; i < nblocks; ++i) {
    EXPECT_EQ(protocol_inner(&state_), kErrorOk);
    EXPECT_LT(state_.offset, 2048);
  }

  EXPECT_CALL(xmodem_, RecvFrame(_, _, _, _, _, _))
      .WillOnce(Return(kErrorXModemEndOfFile));
  EXPECT_EQ(protocol_inner(&state_), kErrorOk);

  // At the end, we expect the offset to be reset to zero.
  EXPECT_EQ(state_.offset, 0);
}

INSTANTIATE_TEST_SUITE_P(
    AllCases, XmodemRecvTests,
    // The values are the rescue mode, the block size and number of blocks.
    testing::Values(std::make_tuple(kRescueModeFirmware, 1024, 2),
                    std::make_tuple(kRescueModeFirmware, 128, 16),
                    std::make_tuple(kRescueModeFirmwareSlotB, 1024, 2),
                    std::make_tuple(kRescueModeFirmwareSlotB, 128, 16),
                    std::make_tuple(kRescueModeOwnerBlock, 1024, 2),
                    std::make_tuple(kRescueModeOwnerBlock, 128, 16),
                    std::make_tuple(kRescueModeBootSvcReq, 1024, 1),
                    std::make_tuple(kRescueModeBootSvcReq, 128, 8),
                    std::make_tuple(kRescueModeNoOp, 1024, 2),
                    std::make_tuple(kRescueModeNoOp, 128, 16)));

class XmodemSendTests
    : public XmodemTest,
      public testing::WithParamInterface<std::tuple<rescue_mode_t, size_t>> {};

// Checks that all download commands send the expected length
// and then switch to the default mode with offset 0 and frame 1.
TEST_P(XmodemSendTests, Download) {
  rescue_mode_t mode;
  rescue_mode_t next_mode;
  size_t payload_len;

  std::tie(mode, payload_len) = GetParam();
  rescue_validate_mode(mode, &state_);
  switch (mode) {
    case kRescueModeNoOp:
    case kRescueModeReboot:
      // NoOp and Reboot do not switch back to the default mode.
      next_mode = mode;
      break;
    default:
      next_mode = state_.default_mode;
  }

  HandleOwnerRead();
  HandleRetentionRam();

  // If the payload length is zero, there is nothing to send.
  if (payload_len != 0) {
    EXPECT_CALL(xmodem_, Send(_, _, payload_len)).WillOnce(Return(kErrorOk));
  }

  // When the protocol calls receive, we'll return out with a TimeoutStart.
  ON_CALL(xmodem_, RecvFrame(_, _, _, _, _, _))
      .WillByDefault(Return(kErrorXModemTimeoutStart));

  rom_error_t expected =
      mode != kRescueModeReboot ? kErrorOk : kErrorRescueReboot;
  EXPECT_EQ(protocol_inner(&state_), expected);
  EXPECT_EQ(state_.offset, 0);
  EXPECT_EQ(state_.frame, 1);
  EXPECT_EQ(state_.mode, next_mode);
}

INSTANTIATE_TEST_SUITE_P(
    AllCases, XmodemSendTests,
    // The values are the rescue mode and expected transfer size.
    testing::Values(std::make_tuple(kRescueModeBootLog, 128),
                    std::make_tuple(kRescueModeBootSvcRsp, 256),
                    std::make_tuple(kRescueModeOpenTitanID, 32),
                    std::make_tuple(kRescueModeOwnerPage0, 2048),
                    std::make_tuple(kRescueModeOwnerPage1, 2048),
                    std::make_tuple(kRescueModeReboot, 0),
                    std::make_tuple(kRescueModeNoOp, 0)));

}  // namespace
}  // namespace rescue_xmodem_unittest
