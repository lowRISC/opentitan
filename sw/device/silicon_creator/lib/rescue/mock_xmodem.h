// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_RESCUE_MOCK_XMODEM_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_RESCUE_MOCK_XMODEM_H_

#include "sw/device/lib/base/global_mock.h"
#include "sw/device/silicon_creator/lib/rescue/xmodem.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace rom_test {
namespace internal {

class MockXmodem : public global_mock::GlobalMock<MockXmodem> {
 public:
  MOCK_METHOD(void, RecvStart, (void *));
  MOCK_METHOD(void, Ack, (void *, bool));
  MOCK_METHOD(void, Cancel, (void *));
  MOCK_METHOD(rom_error_t, RecvFrame,
              (void *, uint32_t, uint8_t *, size_t, size_t *, uint8_t *));
  MOCK_METHOD(rom_error_t, Send, (void *, const void *, size_t));
};

}  // namespace internal

using MockXmodem = testing::StrictMock<internal::MockXmodem>;
using NiceMockXmodem = testing::NiceMock<internal::MockXmodem>;

}  // namespace rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_RESCUE_MOCK_XMODEM_H_
