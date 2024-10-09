// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_MOCK_OWNERSHIP_KEY_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_MOCK_OWNERSHIP_KEY_H_

#include "sw/device/lib/base/global_mock.h"
#include "sw/device/silicon_creator/lib/ownership/ownership_key.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace rom_test {
namespace internal {

/**
 * Mock class for ownership_key.c.
 */
class MockOwnershipKey : public global_mock::GlobalMock<MockOwnershipKey> {
 public:
  MOCK_METHOD(hardened_bool_t, validate,
              (size_t, ownership_key_t, const owner_signature_t *, const void *,
               size_t));
  MOCK_METHOD(rom_error_t, seal_init, ());
  MOCK_METHOD(rom_error_t, seal_page, (size_t));
  MOCK_METHOD(rom_error_t, seal_check, (size_t));
  MOCK_METHOD(rom_error_t, secret_new, ());
};

}  // namespace internal

using MockOwnershipKey = testing::StrictMock<internal::MockOwnershipKey>;

}  // namespace rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_MOCK_OWNERSHIP_KEY_H_
