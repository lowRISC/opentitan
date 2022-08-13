// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_HMAC_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_HMAC_H_

#include "sw/device/lib/base/global_mock.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace rom_test {
namespace internal {

/**
 * Mock class for hmac.c.
 */
class MockHmac : public global_mock::GlobalMock<MockHmac> {
 public:
  MOCK_METHOD(void, sha256_init, ());
  MOCK_METHOD(rom_error_t, sha256_update, (const void *, size_t));
  MOCK_METHOD(rom_error_t, sha256_final, (hmac_digest_t *));
};

}  // namespace internal

using MockHmac = testing::StrictMock<internal::MockHmac>;

}  // namespace rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_HMAC_H_
